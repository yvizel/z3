/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    itp_visitor.h

Abstract:

    Proof-replay visitor that computes a Craig interpolant for a pair (A, B).

    Given a refutation of A & B, with every original clause marked A or B
    (sat::ab_mark) and every variable marked A / B / AB, this visitor builds
    an interpolant as a Z3 expression while the trimmed proof is replayed.
    It is the (A, B)-pair analogue of avy's ItpSequence, which computes a
    sequence interpolant; here there is a single partition and no sequence
    loop.

    The construction is a labeled interpolation system (D'Silva, Kroening,
    Purandare, Weissenbacher, VMCAI 2010): every literal carries a label in
    the lattice {a, b, ab}. Locality forces A-local variables to a and
    B-local variables to b; the labeling mode chooses the label of shared
    (mark AB) variables - b for McMillan (the default and the strongest),
    ab for Huang/Krajicek/Pudlak, a for McMillan's dual (the weakest).

      - Leaf clause c marked A: I(c) = \/ { l in c : label(l) = b }
      - Leaf clause c marked B: I(c) = /\ { ~l : l in c, label(l) = a }
      - Resolution on pivot variable x:
          label a  -> I = I1 \/ I2
          label b  -> I = I1 /\ I2
          label ab -> I = (I1 \/ ~p) /\ (I2 \/ p), p the pivot literal of
                      the premise labelled I2
      - The interpolant is the label of the empty (root) clause.

    Under the default (mcmillan) mode this coincides literally with
    McMillan's system: A-leaves keep their shared literals, B-leaves are
    true, and resolution uses \/ for A-local pivots and /\ otherwise.

    The interpolant ranges over the shared variables only. Each bool_var is
    mapped to a Boolean atom; by default a fresh placeholder constant is
    created per variable, but a caller may inject real atoms (e.g. EUF
    equalities) via set_atom prior to replay, so the resulting expression can
    later be specialized/substituted for the EUF case.

Author:

    Yakir Vizel 2025

--*/
#pragma once

#include "ast/ast.h"
#include "sat/proof_visitor.h"
#include "util/map.h"
#include "util/obj_hashtable.h"
#include "util/hash.h"

namespace sat {

    // Labeling of shared variables in the labeled interpolation system.
    enum class itp_labeling {
        mcmillan,  // shared -> b : strongest interpolant (default)
        hkp,       // shared -> ab: Huang/Krajicek/Pudlak, symmetric
        dual       // shared -> a : McMillan's dual, weakest
    };

    class itp_visitor : public proof_visitor {

        // Per-occurrence literal label of the labeled interpolation system.
        // We use uniform per-variable labels: locality forces A-local
        // variables to a and B-local to b; shared variables follow the
        // labeling mode. Unmarked variables are treated as b, matching the
        // /\-rule they received before labeling was introduced.
        enum class lbl : unsigned char { a, b, ab };

        struct lits_hash {
            unsigned operator()(literal_vector const& v) const {
                return string_hash(std::string_view(reinterpret_cast<char const*>(v.begin()), v.size() * sizeof(literal)), 3);
            }
        };
        struct lits_eq {
            bool operator()(literal_vector const& a, literal_vector const& b) const { return a == b; }
        };

        ast_manager&      m;
        svector<ab_mark>  m_var_mark;     // bool_var -> structural A/B mark (over original clauses)
        ptr_vector<expr>  m_atoms;        // bool_var -> atom (borrowed; pinned in m_atom_refs)
        expr_ref_vector   m_atom_refs;    // owns the atoms
        expr_ref_vector   m_pinned;       // owns interpolant nodes
        ptr_vector<expr>  m_unit_label;   // bool_var -> partial interpolant of its level-0 unit

        // normalized clause literals -> partial interpolant label (borrowed; pinned in m_pinned)
        map<literal_vector, expr*, lits_hash, lits_eq> m_clause_label;

        // clause id -> theory proof hint (borrowed; owned by the proof command layer).
        // An assumption registered here is a theory lemma (e.g. EUF) rather than a
        // plain input clause, and is labelled by a theory-specific procedure.
        u_map<expr*> m_theory_hint;

        // A/B coloring of uninterpreted symbols (over the atoms they occur in):
        // AB means the symbol occurs on both sides (shared/common). Used to decide
        // whether a congruence's function symbol is usable in the summarized side.
        obj_map<func_decl, ab_mark> m_sym_mark;    // uninterpreted symbol -> A/B/AB

        expr*    m_true = nullptr;
        expr*    m_false = nullptr;
        expr_ref m_interpolant;

        itp_labeling m_labeling = itp_labeling::mcmillan;

        ab_mark var_mark(bool_var v) const { return v < m_var_mark.size() ? m_var_mark[v] : MARK_NONE; }
        bool is_shared(bool_var v) const { return var_mark(v) == MARK_AB; }
        bool is_a_local(bool_var v) const { return var_mark(v) == MARK_A; }

        lbl label(bool_var v) const {
            switch (var_mark(v)) {
            case MARK_A:  return lbl::a;
            case MARK_B:  return lbl::b;
            case MARK_AB:
                switch (m_labeling) {
                case itp_labeling::hkp:  return lbl::ab;
                case itp_labeling::dual: return lbl::a;
                default:                 return lbl::b;
                }
            default:      return lbl::b;
            }
        }

        expr* pin(expr* e) { m_pinned.push_back(e); return e; }
        expr* atom(bool_var v);
        expr* lit2expr(literal l);
        expr* mk_or(expr* a, expr* b);
        expr* mk_and(expr* a, expr* b);
        expr* mk_leaf(literal_vector const& clause, ab_mark mark);
        // pivot is the pivot literal as it occurs in the premise labelled l2;
        // the premise labelled l1 contains its negation.
        expr* combine(literal pivot, expr* l1, expr* l2);
        void normalize(literal_vector& c) const;
        expr* clause_label(literal_vector const& lits);
        void set_clause_label(literal_vector const& lits, expr* label);

        bool is_theory(unsigned id) const { return m_theory_hint.contains(id); }
        expr* mk_theory_leaf(unsigned id, literal_vector const& clause, expr* hint, ab_mark mark);

        void compute_symbol_marks();
        void mark_symbols(expr* atom, ab_mark mk);
        ab_mark symbol_mark(func_decl* f) const;  // uninterpreted symbol color

        // EUF interpolation of a theory lemma: parse the negated clause into an
        // (A, B) pair (alpha = literals whose atom is not B-only) and delegate to
        // euf_interpolator. Returns the partial interpolant, or null if the lemma
        // is not handled (non-equality atoms, unhandled conflict shape).
        expr_ref euf_interpolant(literal_vector const& clause);

    public:
        itp_visitor(ast_manager& m):
            m(m), m_atom_refs(m), m_pinned(m), m_interpolant(m) {
            m_true = m.mk_true();
            m_false = m.mk_false();
            m_pinned.push_back(m_true);
            m_pinned.push_back(m_false);
        }

        // Select the labeling of shared variables (default: mcmillan). Must be
        // set before replay.
        void set_labeling(itp_labeling l) { m_labeling = l; }

        // Inject a real atom for a variable (e.g. an EUF equality) before replay.
        void set_atom(bool_var v, expr* a);

        // Register an assumption as a theory lemma carrying its proof hint, so that
        // replay can apply theory-specific (e.g. EUF) interpolation to it. Must be
        // called before replay. The hint is borrowed and must outlive replay.
        void register_theory_clause(unsigned id, expr* hint);

        // The computed interpolant (valid after replay reaches the empty clause).
        expr_ref get_interpolant() const { return m_interpolant; }

        void visit_marks(svector<ab_mark> const& var_marks, svector<ab_mark> const& trail_marks) override;
        void visit_assumption(unsigned id, literal_vector const& clause, ab_mark mark = MARK_NONE) override;
        void visit_inference(unsigned id, literal_vector const& clause, unsigned_vector const& antecedents, ab_mark mark = MARK_NONE) override;
        void visit_delete(unsigned) override {}
        void visit_external_justification(unsigned, int, void*) override {}

        int visitResolvent(literal resolvent, literal p1, proof_clause_ref const& p2) override;
        int visitChainResolvent(literal parent) override;
        int visitChainResolvent(proof_clause_ref const& parent) override;
    };

}
