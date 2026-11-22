/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    euf_interpolator.cpp

Abstract:

    Implementation of the EUF interpolator for an (A, B) conjunction of
    (dis)equalities. See header.

    The interpolant is obtained by colored proof-forest summarization:
      - build the full egraph from all equalities, tagging one side's merges;
      - locate the disequality that the conflict violates;
      - summarize the path between its sides, which yields equalities over
        shared terms (introducing shared function applications at congruence
        color boundaries).

    For a conflict whose violated disequality lies in B, the interpolant is the
    summary of A's contribution; for one in A it is the negation of the summary
    of B's contribution (Itp(A,B) = not Itp(B,A)).

Author:

    Yakir Vizel 2025

--*/

#include "sat/smt/euf_interpolator.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_enode.h"
#include "ast/euf/euf_summary.h"
#include "util/obj_hashtable.h"
#include "util/uint_set.h"
#include "util/obj_pair_hashtable.h"

namespace sat {

    typedef euf_interpolator::atom atom;

    static euf::enode* intern(euf::egraph& eg, expr* e) {
        if (euf::enode* n = eg.find(e))
            return n;
        ptr_vector<euf::enode> args;
        if (is_app(e))
            for (expr* a : *to_app(e))
                args.push_back(intern(eg, a));
        return eg.mk(e, 0, args.size(), args.data());
    }

    // Whether an atom belongs to the given side; gamma (MARK_AB) atoms belong
    // to both sides.
    static bool on_side(atom const& a, bool side_a) {
        return a.side == MARK_AB || a.side == (side_a ? MARK_A : MARK_B);
    }

    // Assert the equalities of one side (including gamma); report whether a
    // disequality of that same side is then violated (the side is
    // unsatisfiable on its own).
    static bool side_unsat(ast_manager& m, svector<atom> const& atoms, bool side_a) {
        euf::egraph eg(m);
        for (auto const& a : atoms) { intern(eg, a.lhs); intern(eg, a.rhs); }
        for (auto const& a : atoms)
            if (on_side(a, side_a) && !a.is_diseq)
                eg.merge(eg.find(a.lhs), eg.find(a.rhs), a.lhs);
        eg.propagate();
        for (auto const& a : atoms)
            if (on_side(a, side_a) && a.is_diseq &&
                eg.find(a.lhs)->get_root() == eg.find(a.rhs)->get_root())
                return true;
        return false;
    }

    // ---------------------------------------------------------------------
    // Certificate construction.
    //
    // The summarizer's clauses (prem -> lhs = rhs) are the runs of the
    // summarized side S. Their derivations, the derivations of their premises
    // by the other side T, and the final derivation of the violated
    // disequality on the conflict side are all obtained independently of the
    // summarizer's traversal: a small egraph is built from the side's equality
    // atoms plus the available premises, closed under congruence, and the
    // proof-forest path between the two terms is read off as explicit
    // refl/assumption/premise/symm/trans/congr steps. Runs are created in
    // layers so that every premise refers to an earlier run.
    // ---------------------------------------------------------------------

    typedef euf_interpolator::cert cert;

    namespace {
        // What an external egraph justification stands for.
        struct source {
            bool     is_atom;
            unsigned index;    // atom index, or run id of the premise
            expr*    lhs;
            expr*    rhs;
        };

        class deriver {
            ast_manager&            m;
            svector<atom> const&    m_atoms;
            euf::egraph             eg;
            ptr_vector<source>      m_sources;   // owned
            svector<cert::step>&    m_steps;
            obj_map<euf::enode, unsigned> m_edge_memo;
            std::string             m_error;
            uint_set                m_used_runs;

            euf::enode* intern(expr* e) {
                if (euf::enode* n = eg.find(e))
                    return n;
                ptr_vector<euf::enode> args;
                if (is_app(e))
                    for (expr* a : *to_app(e))
                        args.push_back(intern(a));
                return eg.mk(e, 0, args.size(), args.data());
            }

            unsigned push(cert::step const& st) {
                m_steps.push_back(st);
                return m_steps.size() - 1;
            }
            unsigned mk_refl(expr* t) { cert::step st; st.kind = cert::rule::refl; st.term = t; return push(st); }
            unsigned mk_symm(unsigned of) { cert::step st; st.kind = cert::rule::symm; st.first = of; return push(st); }
            unsigned mk_trans(unsigned a, unsigned b) { cert::step st; st.kind = cert::rule::trans; st.first = a; st.second = b; return push(st); }

            euf::enode* lca(euf::enode* a, euf::enode* b) {
                obj_hashtable<euf::enode> on_path;
                for (euf::enode* n = a; n; n = n->get_target())
                    on_path.insert(n);
                for (euf::enode* n = b; n; n = n->get_target())
                    if (on_path.contains(n))
                        return n;
                return nullptr;
            }

            // step concluding n.expr = n.target.expr
            unsigned edge(euf::enode* n) {
                unsigned r;
                if (m_edge_memo.find(n, r))
                    return r;
                euf::enode* t = n->get_target();
                euf::justification j = n->get_justification();
                if (j.is_external()) {
                    source* src = j.ext<source>();
                    cert::step st;
                    st.kind = src->is_atom ? cert::rule::assumption : cert::rule::premise;
                    if (src->is_atom) st.atom = src->index; else { st.run = src->index; m_used_runs.insert(src->index); }
                    if (n->get_expr() == src->lhs && t->get_expr() == src->rhs)
                        r = push(st);
                    else if (n->get_expr() == src->rhs && t->get_expr() == src->lhs)
                        r = mk_symm(push(st));
                    else {
                        fail("edge justification does not match its endpoints");
                        r = push(st);
                    }
                }
                else if (j.is_congruence()) {
                    if (j.is_commutative() || !n->get_decl() || n->get_decl() != t->get_decl() || n->num_args() != t->num_args()) {
                        fail("unsupported congruence edge");
                        r = mk_refl(n->get_expr());
                    }
                    else {
                        cert::step st;
                        st.kind = cert::rule::congr;
                        st.f = n->get_decl();
                        for (unsigned i = 0; i < n->num_args(); ++i)
                            st.args.push_back(derive(n->get_arg(i), t->get_arg(i)));
                        r = push(st);
                    }
                }
                else {
                    fail("unsupported justification kind in proof forest");
                    r = mk_refl(n->get_expr());
                }
                m_edge_memo.insert(n, r);
                return r;
            }

            void fail(char const* msg) { if (m_error.empty()) m_error = msg; }

        public:
            deriver(ast_manager& m, svector<atom> const& atoms, svector<cert::step>& steps):
                m(m), m_atoms(atoms), eg(m), m_steps(steps) {
                for (auto const& a : atoms) { intern(a.lhs); intern(a.rhs); }
            }
            ~deriver() { for (source* s : m_sources) dealloc(s); }

            // Assert the equality atoms of one side (gamma atoms belong to both sides).
            void assert_side(bool side_a) {
                for (unsigned i = 0; i < m_atoms.size(); ++i) {
                    auto const& a = m_atoms[i];
                    if (a.is_diseq || !on_side(a, side_a))
                        continue;
                    source* src = alloc(source);
                    *src = { true, i, a.lhs, a.rhs };
                    m_sources.push_back(src);
                    eg.merge(eg.find(a.lhs), eg.find(a.rhs), src);
                }
                eg.propagate();
            }
            // Assert a premise: the conclusion of run `id`.
            void assert_premise(unsigned id, expr* lhs, expr* rhs) {
                intern(lhs); intern(rhs);
                source* src = alloc(source);
                *src = { false, id, lhs, rhs };
                m_sources.push_back(src);
                eg.merge(eg.find(lhs), eg.find(rhs), src);
                eg.propagate();
            }
            bool entails(expr* x, expr* y) {
                euf::enode* nx = intern(x);
                euf::enode* ny = intern(y);
                eg.propagate();
                return nx->get_root() == ny->get_root();
            }
            // derivation of x = y; returns the step index, or UINT_MAX
            unsigned derive(euf::enode* x, euf::enode* y) {
                if (x == y)
                    return mk_refl(x->get_expr());
                euf::enode* l = lca(x, y);
                if (!l) { fail("terms are not connected"); return UINT_MAX; }
                unsigned ix = UINT_MAX, iy = UINT_MAX;
                for (euf::enode* n = x; n != l; n = n->get_target()) {
                    unsigned s = edge(n);
                    ix = ix == UINT_MAX ? s : mk_trans(ix, s);
                }
                for (euf::enode* n = y; n != l; n = n->get_target()) {
                    unsigned s = edge(n);
                    iy = iy == UINT_MAX ? s : mk_trans(iy, s);
                }
                if (iy == UINT_MAX) return ix;
                if (ix == UINT_MAX) return mk_symm(iy);
                return mk_trans(ix, mk_symm(iy));
            }
            bool derive(expr* x, expr* y) {
                euf::enode* nx = intern(x);
                euf::enode* ny = intern(y);
                eg.propagate();
                if (nx->get_root() != ny->get_root()) { fail("terms are not connected"); return false; }
                derive(nx, ny);
                return m_error.empty();
            }
            uint_set const& used_runs() const { return m_used_runs; }
            std::string const& error() const { return m_error; }
        };

        // One Horn clause of the summary.
        struct horn {
            expr_ref_vector prem;
            expr*           lhs;
            expr*           rhs;
            horn(ast_manager& m): prem(m), lhs(nullptr), rhs(nullptr) {}
        };

        bool parse_horn(ast_manager& m, expr* e, horn& h) {
            expr* body = nullptr, * head = e;
            if (m.is_implies(e, body, head)) {
                if (m.is_and(body))
                    for (expr* p : *to_app(body)) h.prem.push_back(p);
                else
                    h.prem.push_back(body);
            }
            return m.is_eq(head, h.lhs, h.rhs);
        }
    }

    // Build the certificate for a conflict whose violated disequality is atom
    // `diseq`, on side `diseq_is_a`, given the summary clauses of the side S
    // opposite to it. In the dual case (disequality in A) the resulting
    // interpolant in the Lean shape is returned through `dual_itp`.
    static void build_cert(ast_manager& m, svector<atom> const& atoms, bool diseq_is_a, unsigned diseq,
                           expr_ref_vector const& sum, cert& c, expr_ref& dual_itp) {
        c.ok = false;
        c.runs.reset();
        c.conflict_side_a = diseq_is_a;
        c.diseq_atom = diseq;
        bool summarize_a = !diseq_is_a;

        // S-runs to build: the summary clauses.
        vector<horn> clauses;
        for (expr* e : sum) {
            horn h(m);
            if (!parse_horn(m, e, h)) { c.error = "unparsable summary clause"; return; }
            clauses.push_back(std::move(h));
        }
        // the distinct premise equalities, each to be derived by a T-run
        expr_ref_vector prem_eqs(m);
        for (auto const& h : clauses)
            for (expr* p : h.prem)
                if (!prem_eqs.contains(p))
                    prem_eqs.push_back(p);

        unsigned_vector clause_run(clauses.size(), UINT_MAX);   // S-run id per clause
        obj_map<expr, unsigned> prem_run;                         // T-run id per premise equality
        auto derived_s = [&](unsigned k) { return clause_run[k] != UINT_MAX; };

        bool progress = true;
        while (progress) {
            progress = false;
            // S-runs whose premises are all available
            for (unsigned k = 0; k < clauses.size(); ++k) {
                if (derived_s(k)) continue;
                horn const& h = clauses[k];
                bool ready = true;
                for (expr* p : h.prem) if (!prem_run.contains(p)) { ready = false; break; }
                if (!ready) continue;
                cert::run r;
                r.side_a = summarize_a;
                r.lhs = h.lhs; r.rhs = h.rhs;
                deriver d(m, atoms, r.steps);
                d.assert_side(summarize_a);
                for (expr* p : h.prem) {
                    expr* pl = nullptr, * pr = nullptr;
                    VERIFY(m.is_eq(p, pl, pr));
                    unsigned id = prem_run[p];
                    r.premises.push_back(id);
                    d.assert_premise(id, pl, pr);
                }
                if (!d.derive(h.lhs, h.rhs)) { c.error = "summary clause not derivable: " + d.error(); return; }
                clause_run[k] = c.runs.size();
                c.runs.push_back(std::move(r));
                progress = true;
            }
            // T-runs for premises derivable from T's atoms and the S-conclusions so far
            for (expr* p : prem_eqs) {
                if (prem_run.contains(p)) continue;
                expr* pl = nullptr, * pr = nullptr;
                VERIFY(m.is_eq(p, pl, pr));
                cert::run r;
                r.side_a = !summarize_a;
                r.lhs = pl; r.rhs = pr;
                deriver d(m, atoms, r.steps);
                d.assert_side(!summarize_a);
                for (unsigned k = 0; k < clauses.size(); ++k)
                    if (derived_s(k))
                        d.assert_premise(clause_run[k], clauses[k].lhs, clauses[k].rhs);
                if (!d.entails(pl, pr)) continue;
                if (!d.derive(pl, pr)) { c.error = "premise not derivable: " + d.error(); return; }
                for (unsigned id : d.used_runs()) r.premises.push_back(id);
                prem_run.insert(p, c.runs.size());
                c.runs.push_back(std::move(r));
                progress = true;
            }
        }
        for (unsigned k = 0; k < clauses.size(); ++k)
            if (!derived_s(k)) { c.error = "summary clause with underivable premises"; return; }

        // final: the conflict side derives the violated disequality's equality
        {
            cert::run& r = c.final;
            r.side_a = diseq_is_a;
            r.steps.reset(); r.premises.reset();
            r.lhs = atoms[diseq].lhs; r.rhs = atoms[diseq].rhs;
            deriver d(m, atoms, r.steps);
            d.assert_side(diseq_is_a);
            for (unsigned k = 0; k < clauses.size(); ++k)
                d.assert_premise(clause_run[k], clauses[k].lhs, clauses[k].rhs);
            if (!d.derive(r.lhs, r.rhs)) { c.error = "conflict not derivable: " + d.error(); return; }
            for (unsigned id : d.used_runs()) r.premises.push_back(id);
        }

        // Interpolant in the Lean shape for the dual case: the A-side runs'
        // Horn clauses and the negative clause of the final premises.
        if (diseq_is_a) {
            expr_ref_vector conj(m);
            for (auto const& r : c.runs) {
                if (!r.side_a) continue;
                expr_ref eq(m.mk_eq(r.lhs, r.rhs), m);
                if (r.premises.empty()) { conj.push_back(eq); continue; }
                expr_ref_vector body(m);
                for (unsigned id : r.premises) body.push_back(m.mk_eq(c.runs[id].lhs, c.runs[id].rhs));
                conj.push_back(m.mk_implies(body.size() == 1 ? body.get(0) : m.mk_and(body), eq));
            }
            expr_ref_vector neg(m);
            for (unsigned id : c.final.premises) neg.push_back(m.mk_eq(c.runs[id].lhs, c.runs[id].rhs));
            if (neg.empty()) conj.push_back(m.mk_false());
            else conj.push_back(m.mk_not(neg.size() == 1 ? neg.get(0) : m.mk_and(neg)));
            dual_itp = conj.size() == 1 ? expr_ref(conj.get(0), m) : expr_ref(m.mk_and(conj), m);
        }
        c.ok = true;
    }

    // Certificate of a side that is inconsistent on its own: the final
    // derivation uses only that side's atoms.
    static void build_trivial_cert(ast_manager& m, svector<atom> const& atoms, bool side_a, cert& c) {
        c.ok = false;
        c.runs.reset();
        c.conflict_side_a = side_a;
        deriver probe(m, atoms, c.final.steps);
        probe.assert_side(side_a);
        for (unsigned i = 0; i < atoms.size(); ++i) {
            auto const& a = atoms[i];
            if (!a.is_diseq || !on_side(a, side_a) || !probe.entails(a.lhs, a.rhs))
                continue;
            c.diseq_atom = i;
            c.final.side_a = side_a;
            c.final.steps.reset(); c.final.premises.reset();
            c.final.lhs = a.lhs; c.final.rhs = a.rhs;
            deriver d(m, atoms, c.final.steps);
            d.assert_side(side_a);
            if (!d.derive(a.lhs, a.rhs)) { c.error = "trivial conflict not derivable: " + d.error(); return; }
            c.ok = true;
            return;
        }
        c.error = "no violated disequality on the inconsistent side";
    }

    expr_ref euf_interpolator::interpolate(svector<atom> const& atoms, std::function<ab_mark(func_decl*)> const& sym_mark, cert* c) {
        expr_ref null(m);
        bool has_a = false, has_b = false;
        for (auto const& a : atoms) { has_a |= a.side != MARK_B; has_b |= a.side != MARK_A; }

        auto mk_conj = [&](expr_ref_vector const& v) -> expr_ref {
            if (v.empty())  return expr_ref(m.mk_true(), m);
            if (v.size() == 1) return expr_ref(v.get(0), m);
            return expr_ref(m.mk_and(v), m);
        };

        // Trivial cases.
        if (has_b && side_unsat(m, atoms, false)) {
            if (c) build_trivial_cert(m, atoms, false, *c);
            return expr_ref(m.mk_true(), m);
        }
        if (has_a && side_unsat(m, atoms, true)) {
            if (c) build_trivial_cert(m, atoms, true, *c);
            return expr_ref(m.mk_false(), m);
        }

        // Locate the disequality the (mixed) conflict violates, and which side it is on.
        int diseq_idx = -1;
        bool diseq_is_a = false;
        {
            euf::egraph eg(m);
            for (auto const& a : atoms) { intern(eg, a.lhs); intern(eg, a.rhs); }
            for (auto const& a : atoms)
                if (!a.is_diseq)
                    eg.merge(eg.find(a.lhs), eg.find(a.rhs), a.lhs);
            eg.propagate();
            for (unsigned i = 0; i < atoms.size(); ++i) {
                auto const& a = atoms[i];
                if (a.is_diseq && eg.find(a.lhs)->get_root() == eg.find(a.rhs)->get_root()) {
                    diseq_idx = i;
                    // A gamma disequality is available to both sides; treat it
                    // like a beta one (summarize A, no negation) - the gamma
                    // conjunct is present in the J & beta & gamma obligation.
                    diseq_is_a = a.side == MARK_A;
                    break;
                }
            }
        }
        if (diseq_idx < 0)
            return null;

        // Summarize the side opposite the violated disequality: a B-side conflict
        // is interpolated by A's contribution, an A-side conflict by B's.
        bool summarize_a = !diseq_is_a;

        // Merge the summarized side first (marked) and close it under
        // congruence before touching the other side. This makes the proof
        // forest maximally colored for the summarized side: any equality that
        // side entails is derived - and marked - in the first phase, so a
        // later other-side merge never usurps a derivation the summarized
        // side could provide (the union-find never re-connects an already
        // connected pair). This is the egraph analogue of colored BCP.
        euf::egraph eg(m);
        for (auto const& a : atoms) { intern(eg, a.lhs); intern(eg, a.rhs); }
        eg.set_mark_justifications(true);
        for (auto const& a : atoms)
            if (!a.is_diseq && on_side(a, summarize_a))
                eg.merge(eg.find(a.lhs), eg.find(a.rhs), a.lhs);
        eg.propagate();
        eg.set_mark_justifications(false);
        for (auto const& a : atoms)
            if (!a.is_diseq && !on_side(a, summarize_a))
                eg.merge(eg.find(a.lhs), eg.find(a.rhs), a.lhs);
        eg.propagate();

        auto const& d = atoms[diseq_idx];
        euf::enode* s = eg.find(d.lhs);
        euf::enode* t = eg.find(d.rhs);
        if (s->get_root() != t->get_root())
            return null;

        // A symbol is usable in the summarized side if it is shared or local to
        // that side (i.e. not local to the opposite side).
        std::function<bool(func_decl*)> sym_colorable = [&](func_decl* f) {
            ab_mark mk = sym_mark(f);
            return summarize_a ? (mk != MARK_B) : (mk != MARK_A);
        };
        // A symbol may occur in the interpolant only if it is shared. Symbols
        // are colored from the original input clauses, so an unmarked symbol
        // occurs in no input clause at all (solver-introduced); it is usable by
        // either side but must never be emitted, i.e. it is not shared.
        std::function<bool(func_decl*)> sym_shared = [&](func_decl* f) {
            ab_mark mk = sym_mark(f);
            if (mk == MARK_NONE)
                IF_VERBOSE(2, verbose_stream() << "itp: symbol " << f->get_name() << " has no A/B mark; treating as not shared\n");
            return mk == MARK_AB;
        };

        // Purification oracle: a separate closure of the summarized side alone
        // (over the full term universe). The summarizer uses it to re-mark
        // other-side path segments whose endpoint equality the summarized side
        // already entails, fusing summarized runs (proof reordering for EUF).
        //
        // With the summarize-side-first merge order above this is provably a
        // no-op: an equality entailed by the summarized side alone is already
        // derived in the first phase, so the (acyclic) proof forest connects
        // its endpoints through phase-1 edges only - marked inputs, or
        // congruences that summarize_congr re-derives and marks itself. The
        // pass is kept as an executable statement of that invariant: if a
        // future change (merge order, justification marking, non-minimal
        // lemma explanations) breaks it, purification becomes live and
        // reports at verbosity 2 instead of silently degrading interpolants.
        euf::egraph eg_s(m);
        for (auto const& a : atoms) { intern(eg_s, a.lhs); intern(eg_s, a.rhs); }
        for (auto const& a : atoms)
            if (!a.is_diseq && on_side(a, summarize_a))
                eg_s.merge(eg_s.find(a.lhs), eg_s.find(a.rhs), a.lhs);
        eg_s.propagate();
        auto side_entails = [&](expr* x, expr* y) {
            euf::enode* nx = eg_s.find(x);
            euf::enode* ny = eg_s.find(y);
            return nx && ny && nx->get_root() == ny->get_root();
        };

        expr_ref_vector sum(m);
        euf::euf_summarizer summ(eg, sum, sym_colorable, sym_shared);
        summ.set_side_entails(side_entails);
        summ.sum_eq(s, t);
        IF_VERBOSE(2, if (summ.num_purified())
                          verbose_stream() << "itp: euf purification fused " << summ.num_purified() << " segment(s)\n");
        expr_ref J = mk_conj(sum);

        // Itp(A,B): summary of A for a B-side conflict. For an A-side conflict
        // the interpolant is built from the exchange structure in the shape of
        // the Lean extraction (A-run Horn clauses and the negative clause of
        // the premises of A's final derivation); this coincides with the
        // negated B summary when B contributes a single run and is a valid
        // interpolant in general, so it also serves as the certified value.
        if (diseq_is_a) {
            cert local;
            cert& cc = c ? *c : local;
            expr_ref dual(m);
            build_cert(m, atoms, true, diseq_idx, sum, cc, dual);
            if (cc.ok)
                return dual;
            IF_VERBOSE(1, verbose_stream() << "itp: dual-case certificate failed (" << cc.error << "); using negated summary\n");
            return expr_ref(m.mk_not(J), m);
        }
        if (c) {
            expr_ref unused(m);
            build_cert(m, atoms, false, diseq_idx, sum, *c, unused);
        }
        return J;
    }

}
