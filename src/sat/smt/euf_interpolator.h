/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    euf_interpolator.h

Abstract:

    EUF interpolation for a conjunction of (dis)equality literals split into an
    (A, B) pair: the negation of a theory lemma. One procedure produces the
    partial interpolant and its certificate.

    Given A (alpha) and B (beta), each a conjunction of equalities and
    disequalities, with A & B unsatisfiable in EUF:

      1. If one side is unsatisfiable on its own the interpolant is true (B)
         or false (A).
      2. Otherwise all equalities are merged in one egraph and the proof of
         the violated disequality is followed. Each side derives what it can
         from its own atoms; what it cannot derive it receives from the other
         side as a "run": an equality between shared terms that the other side
         derives, possibly from runs it received in turn. Where a run would
         end at a term that is not shared, it ends at a shared application
         f(l1..ln) built from shared representatives of the arguments.
      3. The interpolant is read off the runs the conflict depends on: every
         A-run contributes the Horn clause "received equalities => its
         equality", and a conflict on A's side the negation of the equalities
         A's final derivation received.

    The runs and their derivations form the certificate (see `cert`), which is
    exactly the equality-exchange proof of the Lean library, so the
    interpolant returned is the one the certificate denotes.

    A saturating variant of the same exchange is kept as a last resort for
    lemmas the directed procedure cannot handle; `num_exchange` counts them and
    is expected to stay zero.

    Atoms carry a three-valued side tag matching the labels of a labeled
    interpolation system: MARK_A (alpha only), MARK_B (beta only), or MARK_AB
    (gamma - available to both sides). The labeled T-lemma obligations are
    alpha & gamma |= J and J & beta & gamma unsat; gamma equalities are
    assigned to the side opposite the conflict, whose runs make up J.

Author:

    Yakir Vizel 2025

--*/
#pragma once

#include "ast/ast.h"
#include "sat/proof_mark.h"
#include <functional>

namespace sat {

    class euf_interpolator {
        ast_manager&    m;
        expr_ref_vector m_pinned;        // terms created for certificates (shared applications, congruence results)
        unsigned        m_num_exchange = 0;

    public:
        // A single (dis)equality literal of the negated theory clause.
        struct atom {
            expr*   lhs;
            expr*   rhs;
            bool    is_diseq;  // disequality (lhs != rhs) rather than equality
            ab_mark side;      // MARK_A: alpha, MARK_B: beta, MARK_AB: gamma (both sides)
        };

        // Certificate of the lemma and of its partial interpolant, in the shape
        // of the Lean library's equality-exchange proofs (craig-congruence,
        // docs/certificate.md, section "Theory leaves"): a DAG of runs, each a
        // shared equality derived by one side from its own atoms and from
        // conclusions ("premises") of runs of the other side, and a final
        // derivation of the violated disequality's equality on the conflict side.
        struct cert {
            enum class rule { refl, assumption, premise, symm, trans, congr };
            struct step {
                rule            kind;
                expr*           term = nullptr;   // refl
                unsigned        atom = UINT_MAX;  // assumption: index into the atoms vector
                unsigned        run = UINT_MAX;   // premise: run id
                unsigned        first = UINT_MAX; // symm (of), trans (first), 
                unsigned        second = UINT_MAX;// trans
                func_decl*      f = nullptr;      // congr
                unsigned_vector args;             // congr
            };
            struct run {
                bool            side_a;
                expr*           lhs = nullptr;
                expr*           rhs = nullptr;
                unsigned_vector premises;         // run ids of the other side
                svector<step>   steps;            // last step concludes lhs = rhs
            };
            bool            conflict_side_a = false;
            unsigned        diseq_atom = UINT_MAX; // index into the atoms vector
            svector<run>    runs;
            run             final;                 // derivation of the disequality's equality
            bool            ok = false;
            std::string     error;
        };

        euf_interpolator(ast_manager& m): m(m), m_pinned(m) {}

        // Number of lemmas the directed procedure could not handle and which
        // were interpolated by the saturating equality exchange instead.
        unsigned num_exchange() const { return m_num_exchange; }

        // Compute the partial interpolant for the (A, B) pair described by atoms.
        // sym_mark(f) gives the A/B/AB color of an uninterpreted symbol; a term is
        // shared when all its symbols are colored AB. Returns null if no
        // interpolant was found (caller falls back).
        // When c is given, it is filled with a certificate of the result (c->ok
        // tells whether that succeeded; the interpolant is returned regardless).
        expr_ref interpolate(svector<atom> const& atoms, std::function<ab_mark(func_decl*)> const& sym_mark, cert* c = nullptr);
    };

}
