/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    proof_visitor_impl.h

Abstract:

    Concrete implementations of proof visitors for testing and logging.

Author:

    Yakir Vizel 2025

--*/
#pragma once

#include "sat/proof_visitor.h"
#include <iostream>

namespace sat {

    /**
     * Visitor that logs proof steps to a stream.
     */
    class logging_proof_visitor : public proof_visitor {
        std::ostream& m_out;

        void display_clause(literal_vector const& clause) {
            m_out << "{";
            for (unsigned i = 0; i < clause.size(); ++i) {
                if (i > 0) m_out << " ";
                m_out << clause[i];
            }
            m_out << "}";
        }

        void display_clause_ref(proof_clause_ref const& clause) {
            if (clause.is_valid())
                display_clause(clause.m_lits);
            else
                m_out << "<unit>";
        }

    public:
        explicit logging_proof_visitor(std::ostream& out) : m_out(out) {}

        void visit_assumption(unsigned id, literal_vector const& clause, ab_mark mark = MARK_NONE) override {
            m_out << "[" << id << "] ASSUME";
            if (mark != MARK_NONE) m_out << " (" << ab_mark_to_string(mark) << ")";
            m_out << ": ";
            for (literal lit : clause) {
                if (lit.sign()) m_out << "~";
                m_out << lit.var() << " ";
            }
            m_out << "\n";
        }

        void visit_inference(unsigned id, literal_vector const& clause, unsigned_vector const& antecedents, ab_mark mark = MARK_NONE) override {
            m_out << "[" << id << "] INFER";
            if (mark != MARK_NONE) m_out << " (" << ab_mark_to_string(mark) << ")";
            m_out << ": ";
            for (literal lit : clause) {
                if (lit.sign()) m_out << "~";
                m_out << lit.var() << " ";
            }
            m_out << " from [";
            for (unsigned i = 0; i < antecedents.size(); ++i) {
                if (i > 0) m_out << ", ";
                m_out << antecedents[i];
            }
            m_out << "]\n";
        }

        void visit_marks(svector<ab_mark> const& var_marks, svector<ab_mark> const& trail_marks) override {
            bool any = false;
            for (ab_mark m : var_marks) any |= (m != MARK_NONE);
            if (!any)
                return;
            m_out << "VAR MARKS: ";
            for (unsigned v = 0; v < var_marks.size(); ++v)
                if (var_marks[v] != MARK_NONE)
                    m_out << v << "=" << ab_mark_to_string(var_marks[v]) << " ";
            m_out << "\nTRAIL MARKS: ";
            for (unsigned v = 0; v < trail_marks.size(); ++v)
                if (trail_marks[v] != MARK_NONE)
                    m_out << v << "=" << ab_mark_to_string(trail_marks[v]) << " ";
            m_out << "\n";
        }

        void visit_delete(unsigned id) override {
            m_out << "[" << id << "] DELETE\n";
        }

        void visit_external_justification(unsigned id, int theory_id, void* info) override {
            m_out << "[" << id << "] EXT_JUSTIFICATION theory=" << theory_id << "\n";
        }

        void start_replay() override {
            m_out << "--- Starting proof replay ---\n";
        }

        void end_replay() override {
            m_out << "--- Finished proof replay ---\n";
        }

        int visitResolvent(literal parent, literal unit, proof_clause_ref const& reason) override {
            m_out << "RESOLVENT parent=" << parent << " unit=" << unit << " reason=";
            display_clause_ref(reason);
            m_out << "\n";
            return 0;
        }

        int visitChainResolvent(literal parent) override {
            m_out << "CHAIN parent=" << parent << " clauses=[";
            for (unsigned i = 0; i < chainClauses.size(); ++i) {
                if (i > 0) m_out << ", ";
                display_clause_ref(chainClauses[i]);
            }
            m_out << "] pivots=[";
            for (unsigned i = 0; i < chainPivots.size(); ++i) {
                if (i > 0) m_out << " ";
                m_out << chainPivots[i];
            }
            m_out << "]\n";
            return 0;
        }

        int visitChainResolvent(proof_clause_ref const& parent) override {
            m_out << "CHAIN parent=";
            display_clause_ref(parent);
            m_out << " clauses=[";
            for (unsigned i = 0; i < chainClauses.size(); ++i) {
                if (i > 0) m_out << ", ";
                display_clause_ref(chainClauses[i]);
            }
            m_out << "] pivots=[";
            for (unsigned i = 0; i < chainPivots.size(); ++i) {
                if (i > 0) m_out << " ";
                m_out << chainPivots[i];
            }
            m_out << "]\n";
            return 0;
        }
    };

    /**
     * Visitor that collects statistics about the proof.
     */
    class statistics_proof_visitor : public proof_visitor {
        unsigned m_num_assumptions = 0;
        unsigned m_num_inferences = 0;
        unsigned m_num_deletions = 0;
        unsigned m_num_external = 0;
        unsigned m_max_antecedents = 0;

    public:
        void visit_assumption(unsigned, literal_vector const&, ab_mark = MARK_NONE) override {
            ++m_num_assumptions;
        }

        void visit_inference(unsigned, literal_vector const&, unsigned_vector const& antecedents, ab_mark = MARK_NONE) override {
            ++m_num_inferences;
            m_max_antecedents = std::max(m_max_antecedents, static_cast<unsigned>(antecedents.size()));
        }

        void visit_delete(unsigned) override {
            ++m_num_deletions;
        }

        void visit_external_justification(unsigned, int, void*) override {
            ++m_num_external;
        }

        unsigned num_assumptions() const { return m_num_assumptions; }
        unsigned num_inferences() const { return m_num_inferences; }
        unsigned num_deletions() const { return m_num_deletions; }
        unsigned num_external() const { return m_num_external; }
        unsigned max_antecedents() const { return m_max_antecedents; }

        void display(std::ostream& out) const {
            out << "Proof Statistics:\n";
            out << "  Assumptions: " << m_num_assumptions << "\n";
            out << "  Inferences: " << m_num_inferences << "\n";
            out << "  Deletions: " << m_num_deletions << "\n";
            out << "  External Justifications: " << m_num_external << "\n";
            out << "  Max Antecedents: " << m_max_antecedents << "\n";
        }
    };

}
