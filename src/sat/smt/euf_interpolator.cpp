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

    expr_ref euf_interpolator::interpolate(svector<atom> const& atoms, std::function<ab_mark(func_decl*)> const& sym_mark) {
        expr_ref null(m);
        bool has_a = false, has_b = false;
        for (auto const& a : atoms) { has_a |= a.side != MARK_B; has_b |= a.side != MARK_A; }

        auto mk_conj = [&](expr_ref_vector const& v) -> expr_ref {
            if (v.empty())  return expr_ref(m.mk_true(), m);
            if (v.size() == 1) return expr_ref(v.get(0), m);
            return expr_ref(m.mk_and(v), m);
        };

        // Trivial cases.
        if (has_b && side_unsat(m, atoms, false)) return expr_ref(m.mk_true(), m);
        if (has_a && side_unsat(m, atoms, true))  return expr_ref(m.mk_false(), m);

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
        euf::euf_summarizer summ(eg, sum, sym_colorable);
        summ.set_side_entails(side_entails);
        summ.sum_eq(s, t);
        IF_VERBOSE(2, if (summ.num_purified())
                          verbose_stream() << "itp: euf purification fused " << summ.num_purified() << " segment(s)\n");
        expr_ref J = mk_conj(sum);

        // Itp(A,B): summary of A for a B-side conflict; negation of summary of B
        // for an A-side conflict.
        if (diseq_is_a)
            return expr_ref(m.mk_not(J), m);
        return J;
    }

}
