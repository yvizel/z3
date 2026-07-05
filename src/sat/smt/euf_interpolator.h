/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    euf_interpolator.h

Abstract:

    EUF interpolation for a conjunction of (dis)equality literals split into an
    (A, B) pair. Alternative to the egraph-summary approach (euf_summary): it
    computes the interpolant from A's shared-vocabulary consequences.

    Given A (alpha) and B (beta), each a conjunction of equalities and
    disequalities, with A & B unsatisfiable in EUF:

      1. Close A under congruence in an egraph and read off the equalities it
         entails between AB-common (shared) terms.
      2. Assert B together with those shared equalities in a second egraph.
      3. The shared equalities that participate in explaining a B disequality
         that has collapsed are exactly the conflict with B; their conjunction
         is the interpolant (it is entailed by A, inconsistent with B, and over
         shared symbols only).

    Trivial cases are handled up front: B alone unsat -> true, A alone unsat ->
    false. The dual case, where the violated disequality lies in A, is handled by
    swapping the roles of A and B: the interpolant of (A, B) is the negation of
    the interpolant of (B, A).

    Atoms carry a three-valued side tag matching the labels of a labeled
    interpolation system: MARK_A (alpha only), MARK_B (beta only), or MARK_AB
    (gamma - available to both sides). The labeled T-lemma obligations are
    alpha & gamma |= J and J & beta & gamma unsat, so gamma atoms join
    whichever side is being summarized (and both trivial-case checks), which
    is also the colorability-optimal placement: a larger summarized closure
    yields longer single-colored runs and simpler summaries.

Author:

    Yakir Vizel 2025

--*/
#pragma once

#include "ast/ast.h"
#include "sat/proof_mark.h"
#include <functional>

namespace sat {

    class euf_interpolator {
        ast_manager& m;

    public:
        // A single (dis)equality literal of the negated theory clause.
        struct atom {
            expr*   lhs;
            expr*   rhs;
            bool    is_diseq;  // disequality (lhs != rhs) rather than equality
            ab_mark side;      // MARK_A: alpha, MARK_B: beta, MARK_AB: gamma (both sides)
        };

        euf_interpolator(ast_manager& m): m(m) {}

        // Compute the partial interpolant for the (A, B) pair described by atoms.
        // sym_mark(f) gives the A/B/AB color of an uninterpreted symbol; it is used
        // to decide whether a congruence's function symbol is usable in the side
        // being summarized. Returns null if the case is not handled (caller falls back).
        expr_ref interpolate(svector<atom> const& atoms, std::function<ab_mark(func_decl*)> const& sym_mark);
    };

}
