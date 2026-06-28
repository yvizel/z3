/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    itp_visitor.h

Abstract:

    Proof-replay visitor that computes a Craig interpolant for a pair (A, B).

    Given a refutation of A & B, with every original clause marked A or B
    (sat::ab_mark) and every variable marked A / B / AB, this visitor builds
    a McMillan interpolant as a Z3 expression while the trimmed proof is
    replayed. It is the (A, B)-pair analogue of avy's ItpSequence, which
    computes a sequence interpolant; here there is a single partition and no
    sequence loop.

    McMillan's symmetric system, expressed over our markings:

      - Leaf clause c marked A: I(c) = \/ { literal l of c : var(l) is shared }
        (shared = variable mark AB). Literals over A-local variables are
        dropped because they do not occur in B.
      - Leaf clause c marked B: I(c) = true.
      - Resolution on pivot variable x:
          x is A-local (mark A)  -> I = I1 \/ I2
          otherwise (shared / B) -> I = I1 /\ I2
      - The interpolant is the label of the empty (root) clause.

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

    class itp_visitor : public proof_visitor {

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

        // A/B coloring of EUF terms (atoms-only for now). An uninterpreted symbol is
        // marked by the union of the marks of the atoms it occurs in; AB means the
        // symbol occurs on both sides (shared/common). A term's color is derived from
        // its symbols. Interpreted/theory symbols are common and not colored.
        obj_map<func_decl, ab_mark> m_sym_mark;    // uninterpreted symbol -> A/B/AB
        obj_map<expr, ab_mark>      m_term_mark;   // memoized term color (union of symbol marks)

        expr*    m_true = nullptr;
        expr*    m_false = nullptr;
        expr_ref m_interpolant;

        ab_mark var_mark(bool_var v) const { return v < m_var_mark.size() ? m_var_mark[v] : MARK_NONE; }
        bool is_shared(bool_var v) const { return var_mark(v) == MARK_AB; }
        bool is_a_local(bool_var v) const { return var_mark(v) == MARK_A; }

        expr* pin(expr* e) { m_pinned.push_back(e); return e; }
        expr* atom(bool_var v);
        expr* lit2expr(literal l);
        expr* mk_or(expr* a, expr* b);
        expr* mk_and(expr* a, expr* b);
        expr* mk_leaf(literal_vector const& clause, ab_mark mark);
        expr* combine(bool_var pivot, expr* l1, expr* l2);
        void normalize(literal_vector& c) const;
        expr* clause_label(literal_vector const& lits);
        void set_clause_label(literal_vector const& lits, expr* label);

        bool is_theory(unsigned id) const { return m_theory_hint.contains(id); }
        expr* mk_theory_leaf(unsigned id, literal_vector const& clause, expr* hint, ab_mark mark);

        void compute_symbol_marks();
        void mark_symbols(expr* atom, ab_mark mk);
        bool has_b_local_symbol(expr* t);  // t contains a symbol tagged B (MARK_B)

    public:
        itp_visitor(ast_manager& m):
            m(m), m_atom_refs(m), m_pinned(m), m_interpolant(m) {
            m_true = m.mk_true();
            m_false = m.mk_false();
            m_pinned.push_back(m_true);
            m_pinned.push_back(m_false);
        }

        // Inject a real atom for a variable (e.g. an EUF equality) before replay.
        void set_atom(bool_var v, expr* a);

        // Register an assumption as a theory lemma carrying its proof hint, so that
        // replay can apply theory-specific (e.g. EUF) interpolation to it. Must be
        // called before replay. The hint is borrowed and must outlive replay.
        void register_theory_clause(unsigned id, expr* hint);

        // The computed interpolant (valid after replay reaches the empty clause).
        expr_ref get_interpolant() const { return m_interpolant; }

        // A/B coloring queries (AB = shared/common). Valid after visit_marks.
        ab_mark symbol_mark(func_decl* f) const;  // uninterpreted symbol color
        ab_mark term_mark(expr* t);               // union of the term's symbol colors
        bool is_ab_common(expr* t);               // every uninterpreted symbol in t is shared

        // Negate a theory clause and split the resulting conjunction of literals into
        // the (alpha, beta) interpolation pair: a literal goes to beta iff its atom
        // contains a B-local symbol, otherwise to alpha. The conjunction of alpha and
        // of beta is unsatisfiable (the clause is theory-valid), so an interpolant of
        // (alpha, beta) is the clause's partial interpolant.
        void split_theory_clause(literal_vector const& clause, expr_ref_vector& alpha, expr_ref_vector& beta);

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
