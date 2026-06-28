/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    itp_visitor.cpp

Abstract:

    Implementation of the (A, B)-pair interpolation proof-replay visitor.

Author:

    Yakir Vizel 2025

--*/

#include "sat/smt/itp_visitor.h"
#include "ast/ast_pp.h"

namespace sat {

    void itp_visitor::set_atom(bool_var v, expr* a) {
        SASSERT(a && m.is_bool(a));
        m_atoms.reserve(v + 1, nullptr);
        if (m_atoms[v] == a)
            return;
        m_atom_refs.push_back(a);
        m_atoms[v] = a;
    }

    expr* itp_visitor::atom(bool_var v) {
        m_atoms.reserve(v + 1, nullptr);
        if (!m_atoms[v]) {
            std::string name = "itp!" + std::to_string(v);
            expr* a = m.mk_const(symbol(name), m.mk_bool_sort());
            m_atom_refs.push_back(a);
            m_atoms[v] = a;
        }
        return m_atoms[v];
    }

    expr* itp_visitor::lit2expr(literal l) {
        expr* a = atom(l.var());
        return l.sign() ? pin(m.mk_not(a)) : a;
    }

    expr* itp_visitor::mk_or(expr* a, expr* b) {
        if (a == m_true || b == m_true) return m_true;
        if (a == m_false) return b;
        if (b == m_false) return a;
        if (a == b) return a;
        return pin(m.mk_or(a, b));
    }

    expr* itp_visitor::mk_and(expr* a, expr* b) {
        if (a == m_false || b == m_false) return m_false;
        if (a == m_true) return b;
        if (b == m_true) return a;
        if (a == b) return a;
        return pin(m.mk_and(a, b));
    }

    // Leaf labeling (McMillan):
    //   A-clause -> disjunction of its shared literals (false if none)
    //   B-clause -> true
    expr* itp_visitor::mk_leaf(literal_vector const& clause, ab_mark mark) {
        if (mark == MARK_B)
            return m_true;
        if (mark != MARK_A) {
            // Original clauses are required to be A or B; treat an unmarked
            // leaf conservatively as B (does not constrain the interpolant).
            IF_VERBOSE(1, verbose_stream() << "itp: leaf clause without A/B mark, treating as B\n");
            return m_true;
        }
        expr* label = m_false;
        for (literal l : clause)
            if (is_shared(l.var()))
                label = mk_or(label, lit2expr(l));
        return label;
    }

    expr* itp_visitor::combine(bool_var pivot, expr* l1, expr* l2) {
        if (l1 == l2)
            return l1;
        if (is_a_local(pivot))
            return mk_or(l1, l2);
        return mk_and(l1, l2);
    }

    void itp_visitor::normalize(literal_vector& c) const {
        std::sort(c.begin(), c.end());
        unsigned j = 0;
        literal prev = null_literal;
        for (unsigned i = 0; i < c.size(); ++i)
            if (c[i] != prev)
                prev = c[j++] = c[i];
        c.shrink(j);
    }

    void itp_visitor::set_clause_label(literal_vector const& lits, expr* label) {
        literal_vector key(lits);
        normalize(key);
        m_clause_label.insert(key, label);
        if (key.size() == 1) {
            bool_var v = key[0].var();
            m_unit_label.reserve(v + 1, nullptr);
            m_unit_label[v] = label;
        }
    }

    expr* itp_visitor::clause_label(literal_vector const& lits) {
        literal_vector key(lits);
        normalize(key);
        expr* label = nullptr;
        if (m_clause_label.find(key, label))
            return label;
        if (key.size() == 1) {
            bool_var v = key[0].var();
            if (v < m_unit_label.size() && m_unit_label[v])
                return m_unit_label[v];
        }
        IF_VERBOSE(1, verbose_stream() << "itp: missing label for clause " << key << ", using true\n");
        return m_true;
    }

    void itp_visitor::visit_marks(svector<ab_mark> const& var_marks, svector<ab_mark> const&) {
        m_var_mark.reset();
        m_var_mark.append(var_marks);
        m_atoms.reserve(var_marks.size(), nullptr);
        m_unit_label.reserve(var_marks.size(), nullptr);
        compute_symbol_marks();
    }

    // Color uninterpreted symbols by the marks of the atoms they occur in
    // (atoms-only). A symbol seen on both sides becomes AB (shared).
    void itp_visitor::compute_symbol_marks() {
        m_sym_mark.reset();
        m_term_mark.reset();
        for (unsigned v = 0; v < m_atoms.size(); ++v) {
            expr* a = m_atoms[v];
            ab_mark mk = var_mark(v);
            if (a && mk != MARK_NONE)
                mark_symbols(a, mk);
        }
        IF_VERBOSE(2, {
            verbose_stream() << "itp symbol marks:";
            for (auto const& kv : m_sym_mark)
                verbose_stream() << " " << kv.m_key->get_name() << "=" << ab_mark_to_string(kv.m_value);
            verbose_stream() << "\n";
        });
    }

    void itp_visitor::mark_symbols(expr* e, ab_mark mk) {
        ptr_vector<expr> todo;
        todo.push_back(e);
        while (!todo.empty()) {
            expr* c = todo.back();
            todo.pop_back();
            if (!is_app(c))
                continue;
            app* a = to_app(c);
            func_decl* f = a->get_decl();
            if (f->get_family_id() == null_family_id) {  // uninterpreted only
                ab_mark cur = MARK_NONE;
                m_sym_mark.find(f, cur);
                m_sym_mark.insert(f, cur | mk);
            }
            for (expr* arg : *a)
                todo.push_back(arg);
        }
    }

    ab_mark itp_visitor::symbol_mark(func_decl* f) const {
        ab_mark m0 = MARK_NONE;
        m_sym_mark.find(f, m0);
        return m0;
    }

    ab_mark itp_visitor::term_mark(expr* t) {
        ab_mark memo = MARK_NONE;
        if (m_term_mark.find(t, memo))
            return memo;
        ab_mark res = MARK_NONE;
        ptr_vector<expr> todo;
        todo.push_back(t);
        while (!todo.empty()) {
            expr* c = todo.back();
            todo.pop_back();
            if (!is_app(c))
                continue;
            app* a = to_app(c);
            if (a->get_decl()->get_family_id() == null_family_id)
                res |= symbol_mark(a->get_decl());
            for (expr* arg : *a)
                todo.push_back(arg);
        }
        m_term_mark.insert(t, res);
        return res;
    }

    bool itp_visitor::is_ab_common(expr* t) {
        ptr_vector<expr> todo;
        todo.push_back(t);
        while (!todo.empty()) {
            expr* c = todo.back();
            todo.pop_back();
            if (!is_app(c))
                continue;
            app* a = to_app(c);
            func_decl* f = a->get_decl();
            if (f->get_family_id() == null_family_id && symbol_mark(f) != MARK_AB)
                return false;
            for (expr* arg : *a)
                todo.push_back(arg);
        }
        return true;
    }

    void itp_visitor::register_theory_clause(unsigned id, expr* hint) {
        m_theory_hint.insert(id, hint);
    }

    // Partial interpolant of a theory lemma. Unlike a plain input clause, a
    // theory lemma (e.g. an EUF congruence/transitivity step) may mix A and B
    // reasoning, so its interpolant is given by a theory-specific procedure
    // reading `hint`, not by the generic shared-literal projection.
    expr* itp_visitor::mk_theory_leaf(unsigned id, literal_vector const& clause, expr* hint, ab_mark mark) {
        // TODO(EUF): dispatch on the hint (e.g. to_app(hint)->get_name() == "euf"/"cc")
        // and compute the EUF theory-lemma interpolant. Until then fall back to the
        // generic leaf labelling so the interpolant stays well-formed.
        IF_VERBOSE(2, verbose_stream() << "itp: theory clause " << id
                   << " hint " << mk_pp(hint, m) << " (generic leaf for now)\n");
        return mk_leaf(clause, mark);
    }

    void itp_visitor::visit_assumption(unsigned id, literal_vector const& clause, ab_mark mark) {
        expr* label = is_theory(id) ? mk_theory_leaf(id, clause, m_theory_hint[id], mark)
                                    : mk_leaf(clause, mark);
        set_clause_label(clause, label);
    }

    void itp_visitor::visit_inference(unsigned, literal_vector const&, unsigned_vector const&, ab_mark) {
        // The label of an inferred clause is produced by the resolution chain
        // that derives it (visitChainResolvent), so nothing to do here.
    }

    // Single resolution step deriving the unit `resolvent` from the unit
    // assignment of var(p1) and the reason clause p2, pivoting on var(p1).
    int itp_visitor::visitResolvent(literal resolvent, literal p1, proof_clause_ref const& p2) {
        bool_var pivot = p1.var();
        expr* l1 = (pivot < m_unit_label.size() && m_unit_label[pivot]) ? m_unit_label[pivot] : m_true;
        expr* l2 = clause_label(p2.m_lits);
        expr* label = combine(pivot, l1, l2);
        bool_var v = resolvent.var();
        m_unit_label.reserve(v + 1, nullptr);
        m_unit_label[v] = label;
        return 0;
    }

    // Chain resolution deriving the unit `parent`: start from chainClauses[0]
    // and resolve away each pivot using the pivot's unit label.
    int itp_visitor::visitChainResolvent(literal parent) {
        if (chainClauses.empty())
            return 0;
        expr* label = clause_label(chainClauses[0].m_lits);
        for (unsigned i = 0; i < chainPivots.size(); ++i) {
            bool_var pivot = chainPivots[i].var();
            expr* l = (pivot < m_unit_label.size() && m_unit_label[pivot]) ? m_unit_label[pivot] : m_true;
            label = combine(pivot, label, l);
        }
        bool_var v = parent.var();
        m_unit_label.reserve(v + 1, nullptr);
        m_unit_label[v] = label;
        return 0;
    }

    // Chain resolution deriving clause `parent` (or the empty/root clause).
    int itp_visitor::visitChainResolvent(proof_clause_ref const& parent) {
        if (chainClauses.empty())
            return 0;
        expr* label = clause_label(chainClauses[0].m_lits);
        for (unsigned i = 0; i + 1 < chainClauses.size(); ++i) {
            bool_var pivot = chainPivots[i].var();
            proof_clause_ref const& r = chainClauses[i + 1];
            expr* l;
            if (r.is_valid())
                l = clause_label(r.m_lits);
            else
                l = (pivot < m_unit_label.size() && m_unit_label[pivot]) ? m_unit_label[pivot] : m_true;
            label = combine(pivot, label, l);
        }
        if (parent.m_lits.empty())
            m_interpolant = label;  // root: empty clause
        else
            set_clause_label(parent.m_lits, label);
        return 0;
    }

}
