/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    euf_interpolator.cpp

Abstract:

    Implementation of the EUF interpolator for an (A, B) conjunction of
    (dis)equalities. See header.

    The file has three parts: `deriver`, which reads explicit derivation steps
    off an egraph (used by the saturating exchange); the saturating equality
    exchange, kept as a last resort; and `directed`, the proof-directed
    procedure that interpolates every lemma in practice.

Author:

    Yakir Vizel 2025

--*/

#include "sat/smt/euf_interpolator.h"
#include "ast/ast_pp.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_enode.h"
#include "util/obj_hashtable.h"
#include "util/uint_set.h"
#include "util/obj_pair_hashtable.h"
#include "util/buffer.h"
#include <algorithm>

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
    // Derivations from an egraph.
    //
    // `deriver` builds a small egraph from one side's equality atoms plus
    // premises, closes it under congruence, and reads the proof-forest path
    // between two terms off as explicit refl/assumption/premise/symm/trans/
    // congr steps. It serves the saturating exchange below.
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
    }


    // ---------------------------------------------------------------------
    // Equality exchange.
    //
    // A saturating interpolation procedure for the (A, B) pair, used only
    // when the directed procedure below fails. It follows the
    // cooperative congruence-closure scheme the Lean library formalizes
    // (EqualityInterpolationConflict): the two sides alternate, each closing
    // its own equalities together with the shared equalities received so
    // far, and announcing every new equality between shared terms. The pool of
    // shared terms starts with the shared subterms of the lemma and is
    // extended with f(s1..sn) whenever a side has an application f(a1..an)
    // of a shared symbol whose arguments it knows equal to shared terms si -
    // this is what lets a side talk about an application over its own local
    // arguments. The exchange stops when one side violates one of its
    // disequalities.
    //
    // The interpolant is read off the announcements that the final conflict
    // depends on: every such A-announcement contributes the Horn clause
    // "received premises => equality", and an A-side conflict contributes the
    // negative clause of its premises. Every clause is over shared terms by
    // construction, and the certificate is exactly this structure.
    // ---------------------------------------------------------------------

    namespace {
        struct announcement {
            bool  side_a;
            expr* lhs;
            expr* rhs;
        };

        bool is_shared_term(expr* e, std::function<bool(func_decl*)> const& shared, obj_map<expr, bool>& memo) {
            bool r;
            if (memo.find(e, r))
                return r;
            r = true;
            if (is_app(e)) {
                func_decl* f = to_app(e)->get_decl();
                if (f->get_family_id() == null_family_id && !shared(f))
                    r = false;
                for (expr* arg : *to_app(e))
                    if (r && !is_shared_term(arg, shared, memo))
                        r = false;
            }
            else
                r = false;
            memo.insert(e, r);
            return r;
        }
    }

    // The interpolant a certificate denotes, as the Lean checker extracts it
    // (EqualityInterpolationConflict.interpolant): only the runs reachable
    // from the final derivation's premises count. Every reachable A-side run
    // contributes the Horn clause "premises => lhs = rhs"; a conflict on side
    // A adds the negative clause of the final premises. Runs the conflict does
    // not depend on contribute nothing, so a lemma's partial interpolant and
    // its certificate always denote the same formula.
    static expr_ref extract_interpolant(ast_manager& m, cert const& c) {
        bool_vector reach(c.runs.size(), false);
        unsigned_vector todo;
        for (unsigned id : c.final.premises) todo.push_back(id);
        while (!todo.empty()) {
            unsigned id = todo.back();
            todo.pop_back();
            if (id >= c.runs.size() || reach[id]) continue;
            reach[id] = true;
            for (unsigned p : c.runs[id].premises) todo.push_back(p);
        }
        expr_ref_vector conj(m);
        auto body_of = [&](unsigned_vector const& prem) {
            expr_ref_vector body(m);
            for (unsigned id : prem) {
                expr_ref e(m.mk_eq(c.runs[id].lhs, c.runs[id].rhs), m);
                if (!body.contains(e)) body.push_back(e);
            }
            return body;
        };
        for (unsigned i = 0; i < c.runs.size(); ++i) {
            auto const& r = c.runs[i];
            if (!reach[i] || !r.side_a) continue;
            expr_ref eq(m.mk_eq(r.lhs, r.rhs), m);
            expr_ref_vector body = body_of(r.premises);
            expr_ref cl(m);
            if (body.empty()) cl = eq;
            else cl = m.mk_implies(body.size() == 1 ? body.get(0) : m.mk_and(body), eq);
            if (!conj.contains(cl)) conj.push_back(cl);
        }
        if (c.conflict_side_a) {
            expr_ref_vector neg = body_of(c.final.premises);
            if (neg.empty()) conj.push_back(m.mk_false());
            else conj.push_back(m.mk_not(neg.size() == 1 ? neg.get(0) : m.mk_and(neg)));
        }
        if (conj.empty()) return expr_ref(m.mk_true(), m);
        if (conj.size() == 1) return expr_ref(conj.get(0), m);
        return expr_ref(m.mk_and(conj), m);
    }

    static bool exchange(ast_manager& m, svector<atom> const& atoms,
                         std::function<ab_mark(func_decl*)> const& sym_mark,
                         expr_ref_vector& pinned, cert& c, expr_ref& itp) {
        c.ok = false;
        c.runs.reset();
        c.error.clear();
        for (auto const& a : atoms)
            if (a.side != MARK_A && a.side != MARK_B) { c.error = "exchange: atom available to both sides"; return false; }

        std::function<bool(func_decl*)> shared = [&](func_decl* f) { return sym_mark(f) == MARK_AB; };
        obj_map<expr, bool> shared_memo;

        // pool of shared terms
        ptr_vector<expr> pool;
        obj_hashtable<expr> in_pool;
        std::function<void(expr*)> add_subterms = [&](expr* e) {
            if (in_pool.contains(e))
                return;
            if (is_app(e))
                for (expr* arg : *to_app(e))
                    add_subterms(arg);
            if (is_shared_term(e, shared, shared_memo)) {
                in_pool.insert(e);
                pool.push_back(e);
            }
        };
        for (auto const& a : atoms) { add_subterms(a.lhs); add_subterms(a.rhs); }

        vector<announcement> ann;
        // common knowledge: the closure of all announcements over the pool
        euf::egraph known(m);
        unsigned known_pool = 0, known_ann = 0;
        auto sync_known = [&]() {
            for (; known_pool < pool.size(); ++known_pool)
                intern(known, pool[known_pool]);
            for (; known_ann < ann.size(); ++known_ann) {
                euf::enode* x = intern(known, ann[known_ann].lhs);
                euf::enode* y = intern(known, ann[known_ann].rhs);
                known.merge(x, y, ann[known_ann].lhs);
            }
            known.propagate();
        };

        int diseq = -1;
        bool conflict_a = false;
        unsigned const max_rounds = 4 * atoms.size() + 16;
        for (unsigned round = 0; diseq < 0 && round < max_rounds; ++round) {
            bool progress = false;
            for (unsigned k = 0; k < 2 && diseq < 0; ++k) {
                bool side_a = k == 0;
                euf::egraph eg(m);
                for (auto const& a : atoms) { intern(eg, a.lhs); intern(eg, a.rhs); }
                for (expr* t : pool) intern(eg, t);
                for (auto const& a : atoms)
                    if (!a.is_diseq && on_side(a, side_a))
                        eg.merge(eg.find(a.lhs), eg.find(a.rhs), a.lhs);
                for (auto const& an : ann)
                    eg.merge(intern(eg, an.lhs), intern(eg, an.rhs), an.lhs);
                eg.propagate();

                // extend the pool: f(a1..an) with f shared and every ai equal to a pool term
                bool grown = true;
                while (grown) {
                    grown = false;
                    obj_map<euf::enode, expr*> rep;   // root -> first pool term of the class
                    for (expr* t : pool) {
                        euf::enode* r = eg.find(t)->get_root();
                        if (!rep.contains(r))
                            rep.insert(r, t);
                    }
                    ptr_vector<expr> fresh;
                    unsigned sz = eg.nodes().size();
                    for (unsigned i = 0; i < sz; ++i) {
                        euf::enode* n = eg.nodes()[i];
                        expr* e = n->get_expr();
                        if (!is_app(e) || to_app(e)->get_num_args() == 0 || in_pool.contains(e))
                            continue;
                        func_decl* f = to_app(e)->get_decl();
                        if (f->get_family_id() != null_family_id || !shared(f))
                            continue;
                        ptr_buffer<expr> args;
                        bool ok = true;
                        for (unsigned j = 0; ok && j < n->num_args(); ++j) {
                            expr* r = nullptr;
                            ok = rep.find(n->get_arg(j)->get_root(), r);
                            if (ok) args.push_back(r);
                        }
                        if (!ok)
                            continue;
                        expr_ref t(m.mk_app(f, args.size(), args.data()), m);
                        if (in_pool.contains(t))
                            continue;
                        pinned.push_back(t);
                        in_pool.insert(t);
                        pool.push_back(t);
                        fresh.push_back(t);
                    }
                    for (expr* t : fresh) { intern(eg, t); grown = true; }
                    if (grown) { eg.propagate(); progress = true; }
                }

                // conflict on this side?
                for (unsigned i = 0; i < atoms.size(); ++i) {
                    auto const& a = atoms[i];
                    if (a.is_diseq && on_side(a, side_a) && eg.find(a.lhs)->get_root() == eg.find(a.rhs)->get_root()) {
                        diseq = i;
                        conflict_a = side_a;
                        break;
                    }
                }
                if (diseq >= 0)
                    break;

                // announce the shared equalities this side knows and the other does not
                sync_known();
                obj_map<euf::enode, expr*> rep;
                for (expr* t : pool) {
                    euf::enode* r = eg.find(t)->get_root();
                    expr* r0 = nullptr;
                    if (!rep.find(r, r0)) { rep.insert(r, t); continue; }
                    if (known.find(r0)->get_root() == known.find(t)->get_root())
                        continue;
                    ann.push_back({ side_a, r0, t });
                    sync_known();
                    progress = true;
                }
            }
            if (!progress)
                break;
        }
        if (diseq < 0) { c.error = "exchange: no conflict reached"; return false; }

        // Derivations, top-down from the conflict: a derivation on one side may
        // use the announcements the other side made before it.
        c.conflict_side_a = conflict_a;
        c.diseq_atom = diseq;
        unsigned const FINAL = ann.size();
        vector<cert::run> runs;
        runs.resize(ann.size());
        bool_vector needed(ann.size(), false), built(ann.size(), false);
        auto build = [&](unsigned id, cert::run& r) -> bool {
            bool side_a = id == FINAL ? conflict_a : ann[id].side_a;
            r.side_a = side_a;
            r.lhs = id == FINAL ? atoms[diseq].lhs : ann[id].lhs;
            r.rhs = id == FINAL ? atoms[diseq].rhs : ann[id].rhs;
            r.steps.reset();
            r.premises.reset();
            deriver d(m, atoms, r.steps);
            d.assert_side(side_a);
            for (unsigned j = 0; j < std::min(id, (unsigned)ann.size()); ++j)
                if (ann[j].side_a != side_a)
                    d.assert_premise(j, ann[j].lhs, ann[j].rhs);
            if (!d.derive(r.lhs, r.rhs)) { c.error = "exchange: derivation failed: " + d.error(); return false; }
            for (unsigned j : d.used_runs()) {
                r.premises.push_back(j);
                needed[j] = true;
            }
            return true;
        };
        cert::run final;
        if (!build(FINAL, final))
            return false;
        for (unsigned id = ann.size(); id-- > 0; ) {
            if (!needed[id])
                continue;
            if (!build(id, runs[id]))
                return false;
            built[id] = true;
        }
        // compact the run ids
        unsigned_vector new_id(ann.size(), UINT_MAX);
        for (unsigned id = 0; id < ann.size(); ++id)
            if (built[id]) {
                new_id[id] = c.runs.size();
                c.runs.push_back(runs[id]);
            }
        auto renumber = [&](cert::run& r) {
            for (unsigned& q : r.premises) q = new_id[q];
            for (auto& st : r.steps)
                if (st.kind == cert::rule::premise)
                    st.run = new_id[st.run];
        };
        for (auto& r : c.runs) renumber(r);
        renumber(final);
        c.final = final;

        // the interpolant
        auto eq_of = [&](unsigned id) { return expr_ref(m.mk_eq(c.runs[id].lhs, c.runs[id].rhs), m); };
        expr_ref_vector conj(m);
        for (auto const& r : c.runs) {
            if (!r.side_a)
                continue;
            expr_ref eq(m.mk_eq(r.lhs, r.rhs), m);
            if (r.premises.empty()) { conj.push_back(eq); continue; }
            expr_ref_vector body(m);
            for (unsigned id : r.premises) body.push_back(eq_of(id));
            conj.push_back(m.mk_implies(body.size() == 1 ? body.get(0) : m.mk_and(body), eq));
        }
        if (conflict_a) {
            expr_ref_vector neg(m);
            for (unsigned id : c.final.premises) neg.push_back(eq_of(id));
            if (neg.empty()) conj.push_back(m.mk_false());
            else conj.push_back(m.mk_not(neg.size() == 1 ? neg.get(0) : m.mk_and(neg)));
        }
        if (conj.empty()) itp = m.mk_true();
        else if (conj.size() == 1) itp = conj.get(0);
        else itp = m.mk_and(conj);
        c.ok = true;
        return true;
    }

    // Whether e mentions shared uninterpreted symbols only.
    static bool shared_only(expr* e, std::function<ab_mark(func_decl*)> const& sym_mark) {
        ptr_vector<expr> todo;
        obj_hashtable<expr> seen;
        todo.push_back(e);
        while (!todo.empty()) {
            expr* t = todo.back();
            todo.pop_back();
            if (!is_app(t) || seen.contains(t))
                continue;
            seen.insert(t);
            func_decl* f = to_app(t)->get_decl();
            if (f->get_family_id() == null_family_id && sym_mark(f) != MARK_AB)
                return false;
            for (expr* arg : *to_app(t))
                todo.push_back(arg);
        }
        return true;
    }

    // ---------------------------------------------------------------------
    // Directed interpolation.
    //
    // One procedure produces both the partial interpolant of a lemma and its
    // certificate. It follows the proof of the conflict instead of saturating:
    //
    //   - All equality atoms are merged into one egraph (the side opposite the
    //     violated disequality first, so that its edges are preferred). The
    //     proof-forest path between the two sides of the disequality is the
    //     proof to interpolate: atom edges belong to side A or B, congruence
    //     edges belong to nobody and are re-derived through the paths of
    //     their arguments.
    //
    //   - A side S derives an equality x = y along a path by itself: its own
    //     atoms are assumptions, and a congruence is a congr step over S's
    //     derivations of the argument equalities ("S owns the congruence").
    //     A derivation may mention any term; only what crosses between the
    //     sides is constrained.
    //
    //   - What S cannot derive is delegated to the other side O as a run: a
    //     maximal stretch of the path made of O's atoms and of congruences O
    //     owns, concluded as an equality L1 = L2 that S uses as a premise.
    //     O's derivation of the run is built by the same procedure, so it may
    //     in turn use runs of S as premises (the Horn premises of the run).
    //
    //   - The invariant: both ends of a run are shared terms. An end is a
    //     path node if that term is shared. Otherwise the run ends inside a
    //     congruence edge f(a1..an) ~ f(b1..bn) with f shared: every argument
    //     path ai ~ bi is split at a shared term li (recursively, by the same
    //     rule) such that one side derives ai = li and the other li = bi, and
    //     the end is the shared term f(l1..ln), which need not occur in the
    //     lemma. This is the shared representative of a term for a side; it
    //     replaces the summarizer's boundary rewriting.
    //
    //   - Where a run may end in several places the choices are tried in a
    //     fixed order: O keeps a congruence it can derive without help from
    //     S; otherwise the run is cut at a shared node when S can own the
    //     congruence, then inside the congruence, and only then does O own it
    //     with premises from S. Cutting early keeps clauses small and their
    //     premises few.
    //
    // The certificate is the trace of this construction, and the interpolant
    // is what the certificate denotes (extract_interpolant). If no shared end
    // can be found the procedure fails and the caller falls back to the
    // equality exchange.
    // ---------------------------------------------------------------------

    namespace {
        class directed {
            enum : unsigned {
                FAIL = UINT_MAX,
                NONE = UINT_MAX - 1,     // empty derivation (reflexivity at the current term)
                MAX_WORK = 200000,
                MAX_DEPTH = 2000
            };

            struct builder {
                bool                side_a;
                svector<cert::step> steps;
                ptr_vector<expr>    lhs, rhs;    // conclusion of each step
                // conclusion -> a step deriving it
                obj_pair_map<expr, expr, unsigned> known;
                bool_vector         uses_premise;  // per step: does it depend on a run of the other side
                builder(bool a): side_a(a) {}
            };
            struct edge {
                bool     is_atom;
                unsigned atom;
            };
            struct path {
                ptr_vector<euf::enode> nodes;
                svector<edge>          edges;   // edges[i] connects nodes[i] and nodes[i+1]
            };

            ast_manager&            m;
            svector<atom> const&    m_atoms;
            bool_vector const&      m_side;      // per atom: does it belong to side A
            std::function<ab_mark(func_decl*)> const& m_sym_mark;
            expr_ref_vector&        m_pinned;
            cert&                   c;
            euf::egraph             eg;
            unsigned_vector         m_idx;       // m_idx[i] == i; addresses serve as justifications
            obj_map<expr, bool>     m_shared;
            unsigned                m_work = 0;
            unsigned                m_depth = 0;
            // One derivation store per side for the whole lemma: a derived
            // equality is reused wherever that side needs it again, in any run.
            // A run is a root step in its side's store; its own step list is
            // extracted when the run is closed. Steps of attempts that are
            // abandoned stay in the store; they are valid and never extracted.
            builder                 m_store[2] = { builder(false), builder(true) };
            // (side, lhs, rhs) -> id of a run concluding it
            obj_pair_map<expr, expr, unsigned> m_run_of[2];
            bool                    m_bad = false;   // internal inconsistency: give up
            // What a side cannot derive (index 1: side A) / own does not depend
            // on the builder, so failures are remembered.
            obj_pair_hashtable<expr, expr> m_no_derive[2], m_no_own[2];
            std::string             m_error;

            void bad(char const* msg) { if (!m_bad) m_error = msg; m_bad = true; }

            euf::enode* intern(expr* e) {
                if (euf::enode* n = eg.find(e))
                    return n;
                ptr_vector<euf::enode> args;
                if (is_app(e))
                    for (expr* a : *to_app(e))
                        args.push_back(intern(a));
                return eg.mk(e, 0, args.size(), args.data());
            }

            bool shared(expr* e) {
                bool r;
                if (m_shared.find(e, r))
                    return r;
                r = is_app(e);
                if (r) {
                    func_decl* f = to_app(e)->get_decl();
                    if (f->get_family_id() == null_family_id && m_sym_mark(f) != MARK_AB)
                        r = false;
                    for (expr* arg : *to_app(e))
                        if (r && !shared(arg))
                            r = false;
                }
                m_shared.insert(e, r);
                return r;
            }

            // ---- steps ---------------------------------------------------

            unsigned push(builder& b, cert::step const& st, expr* l, expr* r) {
                b.steps.push_back(st);
                b.lhs.push_back(l);
                b.rhs.push_back(r);
                b.known.insert(l, r, b.steps.size() - 1);
                bool dep = false;
                switch (st.kind) {
                case cert::rule::premise: dep = true; break;
                case cert::rule::symm: dep = b.uses_premise[st.first]; break;
                case cert::rule::trans: dep = b.uses_premise[st.first] || b.uses_premise[st.second]; break;
                case cert::rule::congr: for (unsigned a : st.args) dep |= b.uses_premise[a]; break;
                default: break;
                }
                b.uses_premise.push_back(dep);
                return b.steps.size() - 1;
            }
            // a step of b already deriving l = r, or FAIL
            unsigned lookup(builder& b, expr* l, expr* r) {
                unsigned i;
                return b.known.find(l, r, i) ? i : FAIL;
            }
            unsigned refl(builder& b, expr* t) {
                cert::step st; st.kind = cert::rule::refl; st.term = t;
                return push(b, st, t, t);
            }
            unsigned assume(builder& b, unsigned i) {
                cert::step st; st.kind = cert::rule::assumption; st.atom = i;
                return push(b, st, m_atoms[i].lhs, m_atoms[i].rhs);
            }
            unsigned prem(builder& b, unsigned id) {
                cert::step st; st.kind = cert::rule::premise; st.run = id;
                return push(b, st, c.runs[id].lhs, c.runs[id].rhs);
            }
            unsigned symm(builder& b, unsigned s) {
                cert::step st; st.kind = cert::rule::symm; st.first = s;
                return push(b, st, b.rhs[s], b.lhs[s]);
            }
            unsigned trans(builder& b, unsigned s1, unsigned s2) {
                if (b.rhs[s1] != b.lhs[s2]) { bad("transitivity over different middle terms"); return s1; }
                cert::step st; st.kind = cert::rule::trans; st.first = s1; st.second = s2;
                return push(b, st, b.lhs[s1], b.rhs[s2]);
            }
            // concatenation of two derivations, either of which may be empty
            unsigned cat(builder& b, unsigned acc, unsigned s) {
                if (acc == NONE) return s;
                if (s == NONE) return acc;
                return trans(b, acc, s);
            }
            unsigned oriented(builder& b, unsigned s, expr* from, expr* to) {
                if (b.lhs[s] == from && b.rhs[s] == to) return s;
                if (b.lhs[s] == to && b.rhs[s] == from) return symm(b, s);
                bad("edge justification does not match its endpoints");
                return s;
            }
            unsigned congr(builder& b, func_decl* f, unsigned_vector const& args) {
                ptr_buffer<expr> ls, rs;
                for (unsigned a : args) { ls.push_back(b.lhs[a]); rs.push_back(b.rhs[a]); }
                expr* l = m.mk_app(f, ls.size(), ls.data());
                m_pinned.push_back(l);
                expr* r = m.mk_app(f, rs.size(), rs.data());
                m_pinned.push_back(r);
                cert::step st; st.kind = cert::rule::congr; st.f = f; st.args.append(args);
                return push(b, st, l, r);
            }

            // Keep the steps the root depends on, renumbered; collect the runs used.
            void prune(builder const& b, unsigned root, svector<cert::step>& out, unsigned_vector& premises) {
                bool_vector need(b.steps.size(), false);
                need[root] = true;
                for (unsigned i = root + 1; i-- > 0; ) {
                    if (!need[i]) continue;
                    cert::step const& st = b.steps[i];
                    switch (st.kind) {
                    case cert::rule::symm: need[st.first] = true; break;
                    case cert::rule::trans: need[st.first] = true; need[st.second] = true; break;
                    case cert::rule::congr: for (unsigned a : st.args) need[a] = true; break;
                    default: break;
                    }
                }
                unsigned_vector ren(b.steps.size(), UINT_MAX);
                uint_set seen;
                for (unsigned i = 0; i <= root; ++i) {
                    if (!need[i]) continue;
                    cert::step st = b.steps[i];
                    switch (st.kind) {
                    case cert::rule::symm: st.first = ren[st.first]; break;
                    case cert::rule::trans: st.first = ren[st.first]; st.second = ren[st.second]; break;
                    case cert::rule::congr: for (unsigned& a : st.args) a = ren[a]; break;
                    case cert::rule::premise:
                        if (!seen.contains(st.run)) { seen.insert(st.run); premises.push_back(st.run); }
                        break;
                    default: break;
                    }
                    ren[i] = out.size();
                    out.push_back(st);
                }
            }

            // Close a run of side b.side_a concluding l = r; returns its id.
            unsigned finish(builder& b, unsigned root, expr* l, expr* r) {
                unsigned id;
                if (m_run_of[b.side_a].find(l, r, id))
                    return id;
                root = oriented(b, root, l, r);
                if (m_bad) return FAIL;
                cert::run run;
                run.side_a = b.side_a;
                run.lhs = l;
                run.rhs = r;
                prune(b, root, run.steps, run.premises);
                m_pinned.push_back(l);
                m_pinned.push_back(r);
                c.runs.push_back(run);
                m_run_of[b.side_a].insert(l, r, c.runs.size() - 1);
                return c.runs.size() - 1;
            }

            // ---- paths ---------------------------------------------------

            bool edge_of(euf::enode* n, edge& e) {
                euf::justification j = n->get_justification();
                euf::enode* t = n->get_target();
                if (j.is_external()) {
                    e.is_atom = true;
                    e.atom = *j.ext<unsigned>();
                    return true;
                }
                if (j.is_congruence() && !j.is_commutative() && n->get_decl() && n->get_decl() == t->get_decl() && n->num_args() == t->num_args()) {
                    e.is_atom = false;
                    e.atom = UINT_MAX;
                    return true;
                }
                return false;
            }

            bool get_path(euf::enode* x, euf::enode* y, path& p) {
                obj_hashtable<euf::enode> up;
                for (euf::enode* n = x; n; n = n->get_target())
                    up.insert(n);
                euf::enode* l = y;
                while (l && !up.contains(l))
                    l = l->get_target();
                if (!l)
                    return false;
                edge e;
                for (euf::enode* n = x; n != l; n = n->get_target()) {
                    if (!edge_of(n, e)) return false;
                    p.nodes.push_back(n);
                    p.edges.push_back(e);
                }
                p.nodes.push_back(l);
                ptr_vector<euf::enode> down;
                for (euf::enode* n = y; n != l; n = n->get_target())
                    down.push_back(n);
                for (unsigned i = down.size(); i-- > 0; ) {
                    if (!edge_of(down[i], e)) return false;
                    p.edges.push_back(e);
                    p.nodes.push_back(down[i]);
                }
                return true;
            }

            // ---- derivations ---------------------------------------------

            // b's side owns the congruence w ~ u: congr over its derivations of the arguments.
            unsigned own(builder& b, euf::enode* w, euf::enode* u) {
                unsigned known = lookup(b, w->get_expr(), u->get_expr());
                if (known != FAIL)
                    return known;
                if (m_no_own[b.side_a].contains(std::make_pair(w->get_expr(), u->get_expr())))
                    return FAIL;
                unsigned r = own_core(b, w, u);
                if (r == FAIL && !m_bad)
                    m_no_own[b.side_a].insert(std::make_pair(w->get_expr(), u->get_expr()));
                return r;
            }

            unsigned own_core(builder& b, euf::enode* w, euf::enode* u) {
                unsigned_vector args;
                for (unsigned i = 0; i < w->num_args(); ++i) {
                    euf::enode* x = w->get_arg(i), * y = u->get_arg(i);
                    unsigned s;
                    if (x == y)
                        s = refl(b, x->get_expr());
                    else {
                        path q;
                        if (!get_path(x, y, q)) return FAIL;
                        s = derive(b, q, 0, q.nodes.size() - 1);
                    }
                    if (s == FAIL) return FAIL;
                    args.push_back(s);
                }
                return congr(b, w->get_decl(), args);
            }

            // End a run inside the congruence w ~ u: a shared term L = f(l1..ln)
            // with x deriving w = L (step sx) and y deriving L = u (step sy).
            bool cut(builder& x, builder& y, euf::enode* w, euf::enode* u, expr*& L, unsigned& sx, unsigned& sy) {
                func_decl* f = w->get_decl();
                if (f->get_family_id() == null_family_id && m_sym_mark(f) != MARK_AB)
                    return false;
                ptr_buffer<expr> ls;
                unsigned_vector ax, ay;
                for (unsigned i = 0; i < w->num_args(); ++i) {
                    euf::enode* p = w->get_arg(i), * q = u->get_arg(i);
                    expr* l = nullptr;
                    unsigned a = FAIL, b = FAIL;
                    if (p == q) {
                        l = p->get_expr();
                        if (!shared(l)) return false;
                        a = refl(x, l);
                        b = refl(y, l);
                    }
                    else {
                        path pq;
                        if (!get_path(p, q, pq)) return false;
                        if (!split(x, y, pq, l, a, b)) return false;
                    }
                    ls.push_back(l);
                    ax.push_back(a);
                    ay.push_back(b);
                }
                L = m.mk_app(f, ls.size(), ls.data());
                m_pinned.push_back(L);
                sx = congr(x, f, ax);
                sy = congr(y, f, ay);
                return !m_bad;
            }

            // Split the path Q between x (coming from its start) and y (coming from
            // its end) at a shared term l: x derives Q.start = l, y derives l = Q.end.
            bool split(builder& x, builder& y, path const& Q, expr*& l, unsigned& sx, unsigned& sy) {
                unsigned n = Q.nodes.size() - 1;
                // the natural place is where y's atoms begin
                unsigned a = n;
                for (unsigned i = 0; i < n; ++i)
                    if (Q.edges[i].is_atom && m_side[Q.edges[i].atom] == y.side_a) { a = i; break; }
                unsigned_vector order;
                for (unsigned t = a + 1; t-- > 0; ) order.push_back(t);
                for (unsigned t = a + 1; t <= n; ++t) order.push_back(t);
                for (unsigned t : order) {
                    expr* e = Q.nodes[t]->get_expr();
                    if (!shared(e)) continue;
                    unsigned s1 = derive(x, Q, 0, t);
                    unsigned s2 = s1 == FAIL ? FAIL : derive(y, Q, t, n);
                    if (s1 != FAIL && s2 != FAIL) { l = e; sx = s1; sy = s2; return true; }
                    if (m_bad) return false;
                }
                // no shared node works: split inside a congruence edge
                for (unsigned t : order) {
                    if (t == n || Q.edges[t].is_atom) continue;
                    unsigned s1 = derive(x, Q, 0, t);
                    expr* L = nullptr;
                    unsigned cx = FAIL, cy = FAIL;
                    if (s1 != FAIL && cut(x, y, Q.nodes[t], Q.nodes[t + 1], L, cx, cy)) {
                        unsigned s2 = derive(y, Q, t + 1, n);
                        if (s2 != FAIL) { l = L; sx = trans(x, s1, cx); sy = trans(y, cy, s2); return !m_bad; }
                    }
                    if (m_bad) return false;
                }
                return false;
            }

            // b's side derives P.nodes[lo] = P.nodes[hi]. Returns the step, or FAIL.
            unsigned derive(builder& b, path const& P, unsigned lo, unsigned hi) {
                expr* l = P.nodes[lo]->get_expr(), * r = P.nodes[hi]->get_expr();
                unsigned known = lookup(b, l, r);
                if (known != FAIL)
                    return known;
                if (m_no_derive[b.side_a].contains(std::make_pair(l, r)))
                    return FAIL;
                unsigned s = derive_core(b, P, lo, hi);
                if (s == FAIL && !m_bad)
                    m_no_derive[b.side_a].insert(std::make_pair(l, r));
                return s;
            }

            unsigned derive_core(builder& b, path const& P, unsigned lo, unsigned hi) {
                if (m_bad)
                    return FAIL;
                if (++m_work > MAX_WORK || m_depth > MAX_DEPTH) {
                    bad(m_work > MAX_WORK ? "work limit reached" : "depth limit reached");
                    return FAIL;
                }
                flet<unsigned> _depth(m_depth, m_depth + 1);
                bool S = b.side_a;
                auto ex = [&](unsigned t) { return P.nodes[t]->get_expr(); };
                auto atom_of = [&](unsigned t, bool side) { return P.edges[t].is_atom && m_side[P.edges[t].atom] == side; };
                auto is_congr = [&](unsigned t) { return !P.edges[t].is_atom; };
                unsigned_vector acc_at;                       // acc_at[t - lo]: derivation of nodes[lo] = nodes[t]
                acc_at.resize(hi - lo + 1, NONE);
                auto at = [&](unsigned t) -> unsigned& { return acc_at[t - lo]; };

                unsigned t = lo;
                while (t < hi) {
                    if (atom_of(t, S)) {
                        unsigned s = oriented(b, assume(b, P.edges[t].atom), ex(t), ex(t + 1));
                        at(t + 1) = cat(b, at(t), s);
                        ++t;
                        continue;
                    }
                    if (is_congr(t)) {
                        unsigned s = own(b, P.nodes[t], P.nodes[t + 1]);
                        if (s != FAIL) {
                            at(t + 1) = cat(b, at(t), s);
                            ++t;
                            continue;
                        }
                        if (m_bad) return FAIL;
                    }

                    // ---- a run of the other side starts here ----
                    builder& R = m_store[!S];
                    expr* L1 = nullptr, * L2 = nullptr, * L = nullptr;
                    unsigned sS = NONE;      // b's derivation of nodes[lo] = L1
                    unsigned racc = NONE;    // R's derivation of L1 = nodes[cur]
                    unsigned cur = t;
                    bool started = false;
                    unsigned sx = FAIL, sy = FAIL;

                    // left end of the run
                    if (is_congr(t)) {
                        if (cut(b, R, P.nodes[t], P.nodes[t + 1], L, sx, sy)) {
                            L1 = L; sS = cat(b, at(t), sx); racc = sy; cur = t + 1; started = true;
                        }
                        else {
                        }
                        if (!started && !m_bad && shared(ex(t))) {
                            unsigned s = own(R, P.nodes[t], P.nodes[t + 1]);
                            if (s != FAIL) { L1 = ex(t); sS = at(t); racc = s; cur = t + 1; started = true; }
                            
                        }
                    }
                    else if (shared(ex(t))) {
                        L1 = ex(t); sS = at(t); cur = t; started = true;
                    }
                    // the term here is not shared: the run starts further left,
                    // inside or before a congruence b's side owned so far
                    for (unsigned k = t; !started && !m_bad && k-- > lo && is_congr(k); ) {
                        if (cut(b, R, P.nodes[k], P.nodes[k + 1], L, sx, sy)) {
                            unsigned s2 = derive(R, P, k + 1, t);
                            if (s2 != FAIL) { L1 = L; sS = cat(b, at(k), sx); racc = trans(R, sy, s2); cur = t; started = true; break; }
                        }
                        if (shared(ex(k))) {
                            unsigned s2 = derive(R, P, k, t);
                            if (s2 != FAIL) { L1 = ex(k); sS = at(k); racc = s2; cur = t; started = true; break; }
                        }
                    }
                    if (!started || m_bad)
                        return FAIL;

                    // extend the run and find its right end
                    unsigned sStub = NONE;       // b's derivation of L2 = nodes[next]
                    unsigned next = cur;
                    bool last_congr = false;     // the last edge R consumed is a congruence it owns
                    unsigned last_racc = NONE;
                    while (true) {
                        if (cur == hi || atom_of(cur, S)) {
                            if (shared(ex(cur))) { L2 = ex(cur); next = cur; break; }
                            // must end here but cannot: end inside the congruence just consumed
                            if (!last_congr) return FAIL;
                            racc = last_racc;
                            if (!cut(R, b, P.nodes[cur - 1], P.nodes[cur], L, sx, sy)) return FAIL;
                            racc = cat(R, racc, sx); sStub = sy; L2 = L; next = cur;
                            break;
                        }
                        if (atom_of(cur, !S)) {
                            unsigned s = oriented(R, assume(R, P.edges[cur].atom), ex(cur), ex(cur + 1));
                            racc = cat(R, racc, s);
                            last_congr = false;
                            ++cur;
                            continue;
                        }
                        // a congruence
                        unsigned s = own(R, P.nodes[cur], P.nodes[cur + 1]);
                        bool own_ok = s != FAIL;
                        if (own_ok && !R.uses_premise[s]) {          // derived without help
                            last_congr = true; last_racc = racc;
                            racc = cat(R, racc, s);
                            ++cur;
                            continue;
                        }
                        if (m_bad) return FAIL;
                        // end at this node if it is shared and b's side can take over
                        if (shared(ex(cur))) {
                            unsigned s2 = own(b, P.nodes[cur], P.nodes[cur + 1]);
                            if (m_bad) return FAIL;
                            if (s2 != FAIL) { L2 = ex(cur); next = cur; break; }
                        }
                        // end inside the congruence
                        {
                            if (cut(R, b, P.nodes[cur], P.nodes[cur + 1], L, sx, sy)) {
                                racc = cat(R, racc, sx); sStub = sy; L2 = L; next = cur + 1;
                                break;
                            }
                            if (m_bad) return FAIL;
                        }
                        // the run passes through, with premises from b's side
                        if (!own_ok) return FAIL;
                        last_congr = true; last_racc = racc;
                        racc = cat(R, racc, s);
                        ++cur;
                    }
                    if (m_bad) return FAIL;

                    unsigned accn = sS;
                    if (racc == NONE) {
                        if (L1 != L2) return FAIL;
                    }
                    else if (L1 != L2) {
                        unsigned id = finish(R, racc, L1, L2);
                        if (id == FAIL) return FAIL;
                        accn = cat(b, accn, prem(b, id));
                    }
                    accn = cat(b, accn, sStub);
                    if (next <= t && accn == at(t)) return FAIL;     // no progress
                    at(next) = accn;
                    t = next;
                }
                if (m_bad) return FAIL;
                unsigned r = at(hi);
                return r == NONE ? refl(b, ex(lo)) : r;
            }

            // Drop runs the final derivation does not depend on, renumbering the rest.
            void compact() {
                bool_vector reach(c.runs.size(), false);
                unsigned_vector todo;
                todo.append(c.final.premises);
                while (!todo.empty()) {
                    unsigned id = todo.back();
                    todo.pop_back();
                    if (reach[id]) continue;
                    reach[id] = true;
                    todo.append(c.runs[id].premises);
                }
                unsigned_vector ren(c.runs.size(), UINT_MAX);
                svector<cert::run> kept;
                for (unsigned i = 0; i < c.runs.size(); ++i)
                    if (reach[i]) { ren[i] = kept.size(); kept.push_back(c.runs[i]); }
                auto fix = [&](cert::run& r) {
                    for (unsigned& p : r.premises) p = ren[p];
                    for (auto& st : r.steps)
                        if (st.kind == cert::rule::premise) st.run = ren[st.run];
                };
                for (auto& r : kept) fix(r);
                fix(c.final);
                c.runs.reset();
                c.runs.append(kept);
            }

        public:
            // `use[i]` selects the atoms taking part; equalities of side
            // `first_a` are merged first.
            directed(ast_manager& m, svector<atom> const& atoms, bool_vector const& side, bool_vector const& use,
                     bool first_a, std::function<ab_mark(func_decl*)> const& sym_mark, expr_ref_vector& pinned, cert& c):
                m(m), m_atoms(atoms), m_side(side), m_sym_mark(sym_mark), m_pinned(pinned), c(c), eg(m) {
                for (unsigned i = 0; i < atoms.size(); ++i)
                    m_idx.push_back(i);
                for (auto const& a : atoms) { intern(a.lhs); intern(a.rhs); }
                for (unsigned phase = 0; phase < 2; ++phase) {
                    for (unsigned i = 0; i < atoms.size(); ++i) {
                        auto const& a = atoms[i];
                        if (!use[i] || a.is_diseq || a.lhs == a.rhs || (side[i] == first_a) != (phase == 0))
                            continue;
                        eg.merge(eg.find(a.lhs), eg.find(a.rhs), &m_idx[i]);
                    }
                    eg.propagate();
                }
            }

            bool violated(unsigned i) {
                return eg.find(m_atoms[i].lhs)->get_root() == eg.find(m_atoms[i].rhs)->get_root();
            }

            // Build the certificate of the conflict on disequality `diseq`.
            bool run(unsigned diseq) {
                c.ok = false;
                c.runs.reset();
                c.error.clear();
                bool conflict_a = m_side[diseq];
                builder& F = m_store[conflict_a];
                euf::enode* s = eg.find(m_atoms[diseq].lhs), * t = eg.find(m_atoms[diseq].rhs);
                unsigned root;
                if (s == t)
                    root = refl(F, s->get_expr());
                else {
                    path p;
                    if (!get_path(s, t, p)) { c.error = "unsupported justification in the proof forest"; return false; }
                    root = derive(F, p, 0, p.nodes.size() - 1);
                }
                if (root == FAIL || m_bad) {
                    c.error = m_bad ? m_error : "no shared end for a run";
                    c.runs.reset();
                    return false;
                }
                root = oriented(F, root, m_atoms[diseq].lhs, m_atoms[diseq].rhs);
                c.conflict_side_a = conflict_a;
                c.diseq_atom = diseq;
                c.final.side_a = conflict_a;
                c.final.lhs = m_atoms[diseq].lhs;
                c.final.rhs = m_atoms[diseq].rhs;
                c.final.steps.reset();
                c.final.premises.reset();
                prune(F, root, c.final.steps, c.final.premises);
                compact();
                c.ok = !m_bad;
                return c.ok;
            }
        };
    }


    expr_ref euf_interpolator::interpolate(svector<atom> const& atoms, std::function<ab_mark(func_decl*)> const& sym_mark, cert* c) {
        expr_ref null(m);
        cert local;
        cert& cc = c ? *c : local;
        cc.ok = false;
        bool has_a = false, has_b = false;
        for (auto const& a : atoms) { has_a |= a.side != MARK_B; has_b |= a.side != MARK_A; }
        bool_vector side, use;

        // One side is inconsistent on its own: the interpolant is true (B) or
        // false (A), certified by that side's derivation of its conflict.
        for (unsigned k = 0; k < 2; ++k) {
            bool side_a = k == 1;
            if (!(side_a ? has_a : has_b) || !side_unsat(m, atoms, side_a))
                continue;
            side.reset();
            use.reset();
            for (auto const& a : atoms) { side.push_back(side_a); use.push_back(on_side(a, side_a)); }
            directed d(m, atoms, side, use, side_a, sym_mark, m_pinned, cc);
            for (unsigned i = 0; i < atoms.size(); ++i)
                if (use[i] && atoms[i].is_diseq && d.violated(i)) {
                    d.run(i);
                    break;
                }
            return expr_ref(side_a ? m.mk_false() : m.mk_true(), m);
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
                    // A gamma disequality is available to both sides; it is
                    // treated as a beta one.
                    diseq_is_a = a.side == MARK_A;
                    break;
                }
            }
        }
        if (diseq_idx < 0)
            return null;

        // Gamma atoms (label ab) are available to both sides. The labeled
        // T-lemma obligations, alpha & gamma |= J and J & beta & gamma unsat,
        // hold for any assignment of the gamma equalities to one side; they
        // go to the side opposite the conflict, the one whose runs make up
        // the interpolant, which gives the longest runs.
        side.reset();
        use.reset();
        for (auto const& a : atoms) {
            side.push_back(a.side == MARK_A || (a.side == MARK_AB && !a.is_diseq && !diseq_is_a));
            use.push_back(true);
        }
        {
            directed d(m, atoms, side, use, !diseq_is_a, sym_mark, m_pinned, cc);
            if (d.run(diseq_idx)) {
                expr_ref result = extract_interpolant(m, cc);
                if (shared_only(result, sym_mark))
                    return result;
                cc.error = "non-shared symbol in the interpolant";
            }
        }

        // Last resort. The directed procedure found no shared end for some
        // run; saturate instead. This is not expected to happen: the lemma is
        // printed at verbosity 2 so the missing case can be added.
        IF_VERBOSE(2, {
            verbose_stream() << "itp: directed interpolation failed (" << cc.error << "), using equality exchange\n";
            for (auto const& a : atoms)
                verbose_stream() << "  " << (a.side == MARK_A ? "A " : a.side == MARK_B ? "B " : "AB ")
                                 << mk_pp(a.lhs, m) << (a.is_diseq ? " != " : " = ") << mk_pp(a.rhs, m) << "\n";
        });
        ++m_num_exchange;
        expr_ref ex(m);
        if (exchange(m, atoms, sym_mark, m_pinned, cc, ex)) {
            expr_ref denoted = extract_interpolant(m, cc);
            if (shared_only(denoted, sym_mark))
                return denoted;
            return ex;
        }
        IF_VERBOSE(0, verbose_stream() << "itp: equality exchange failed (" << cc.error << "); the lemma has no partial interpolant\n");
        cc.ok = false;
        return null;
    }


}
