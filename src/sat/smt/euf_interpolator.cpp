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

    // Assert the equalities of one side; report whether a disequality of that
    // same side is then violated (the side is unsatisfiable on its own).
    static bool side_unsat(ast_manager& m, svector<atom> const& atoms, bool side_a) {
        euf::egraph eg(m);
        for (auto const& a : atoms) { intern(eg, a.lhs); intern(eg, a.rhs); }
        for (auto const& a : atoms)
            if (a.is_a == side_a && !a.is_diseq)
                eg.merge(eg.find(a.lhs), eg.find(a.rhs), a.lhs);
        eg.propagate();
        for (auto const& a : atoms)
            if (a.is_a == side_a && a.is_diseq &&
                eg.find(a.lhs)->get_root() == eg.find(a.rhs)->get_root())
                return true;
        return false;
    }

    expr_ref euf_interpolator::interpolate(svector<atom> const& atoms, std::function<ab_mark(func_decl*)> const& sym_mark) {
        expr_ref null(m);
        bool has_a = false, has_b = false;
        for (auto const& a : atoms) { has_a |= a.is_a; has_b |= !a.is_a; }

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
                    diseq_is_a = a.is_a;
                    break;
                }
            }
        }
        if (diseq_idx < 0)
            return null;

        // Summarize the side opposite the violated disequality: a B-side conflict
        // is interpolated by A's contribution, an A-side conflict by B's.
        bool summarize_a = !diseq_is_a;

        euf::egraph eg(m);
        for (auto const& a : atoms) { intern(eg, a.lhs); intern(eg, a.rhs); }
        eg.set_mark_justifications(true);
        for (auto const& a : atoms)
            if (!a.is_diseq && a.is_a == summarize_a)
                eg.merge(eg.find(a.lhs), eg.find(a.rhs), a.lhs);
        eg.propagate();
        eg.set_mark_justifications(false);
        for (auto const& a : atoms)
            if (!a.is_diseq && a.is_a != summarize_a)
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

        expr_ref_vector sum(m);
        euf::euf_summarizer summ(eg, sum, sym_colorable);
        summ.sum_eq(s, t);
        expr_ref J = mk_conj(sum);

        // Itp(A,B): summary of A for a B-side conflict; negation of summary of B
        // for an A-side conflict.
        if (diseq_is_a)
            return expr_ref(m.mk_not(J), m);
        return J;
    }

}
