/*++
  Copyright (c) 2025 Microsoft Corporation

  Module Name:

    proof_replay_validator.h

  Abstract:
    
    Proof replay validator - validates trimmed proofs through conflict analysis.
    This class reconstructs solver state step-by-step and verifies each inference
    is correct via RUP (Reverse Unit Propagation).

  Author:

    Yakir Vizel 2025

  Notes:
  
    Similar to proof_trim but designed for replay/validation rather than trimming.
    Uses conflict analysis to verify inferences are sound.

--*/

#pragma once

#include "util/params.h"
#include "util/statistics.h"
#include "sat/sat_clause.h"
#include "sat/sat_types.h"
#include "sat/sat_solver.h"
#include "sat/proof_visitor.h"

namespace sat {

    class proof_replay_validator {
        solver         s;
        literal_vector m_clause, m_clause2, m_conflict;
        uint_set       m_in_deps;
        uint_set       m_in_clause;
        uint_set       m_in_coi;
        clause*        m_conflict_clause = nullptr;
        vector<std::tuple<unsigned, literal_vector, clause*, bool, bool>> m_trail;

        struct hash {
            unsigned operator()(literal_vector const& v) const {
                return string_hash(std::string_view((char const*)v.begin(), v.size()*sizeof(literal)), 3);
            }
        };
        struct eq {
            bool operator()(literal_vector const& a, literal_vector const& b) const {
                return a == b;
            }
        };

        struct clause_info {
            clause_vector m_clauses;
            unsigned      m_id = 0;
            bool          m_verified = false;
            bool          m_in_core = false;
        };

        map<literal_vector, clause_info, hash, eq>   m_clauses;
        bool_vector                         m_propagated;
        uint_set                            m_units;
        unsigned                            m_verified_count;
        unsigned                            m_skipped_count;
        unsigned                            m_trace_start = 0;

        // Private methods
        void del(literal_vector const& cl, clause* cp);

        void add_dependency(literal lit);
        void add_dependency(justification j);
        void add_verified(bool_var v);
        void add_verified(literal l, justification j);
        bool in_verified(literal_vector const& cl) const;
        clause* del(literal_vector const& cl);
        void insert_dep(unsigned dep);
        bool unit_or_binary_occurs();
        void normalize_clause(literal_vector& cl) const;
        bool mk_proof_clause(literal consequent, justification js, proof_clause_ref& out);
        bool should_resolve(literal lit) const;
        void mark_core(proof_clause_ref const& c);
        unsigned max_level(proof_clause_ref const& c) const;
        bool subsumes(literal_vector const& a, literal_vector const& b) const;
        bool traverse(proof_visitor& v, proof_clause_ref const& proof_clause, literal_vector& out_learnt);
        void set_solver_conflict(literal_vector const& cl, clause* cp);
        void traceLevel0(proof_visitor& v, unsigned start, unsigned end);
        void set_conflict(literal_vector const& c, clause* cp) { 
            m_conflict.reset(); 
            m_conflict.append(c); 
            m_conflict_clause = cp;
        }
        
    public:

        proof_replay_validator(params_ref const& p, reslimit& lim);

        bool_var mk_var() { return s.mk_var(true, true); }
        void init_clause() { m_clause.reset(); }
        void add_literal(bool_var v, bool sign) { m_clause.push_back(literal(v, sign)); }
        unsigned num_vars() { return s.num_vars(); }

        void assume(unsigned id, bool is_initial = true);
        void del();
        void infer(unsigned id);
        bool infer(unsigned id, proof_visitor& v);
        void updt_params(params_ref const& p) { s.updt_params(p); }

        void replay(vector<std::pair<unsigned, unsigned_vector>> const& proof,
                    vector<std::tuple<unsigned, literal_vector, clause*, bool, bool>> const& trail,
                    proof_visitor& v,
                    std::ostream& out,
                    bool has_terminal_empty_clause,
                    unsigned terminal_empty_clause_id,
                    svector<ab_mark> const& clause_marks = svector<ab_mark>(),
                    svector<ab_mark> const& var_marks = svector<ab_mark>(),
                    svector<ab_mark> const& trail_marks = svector<ab_mark>());

        // Main validation method - replays and validates trimmed proof
        void validate_proof(vector<std::pair<unsigned, unsigned_vector>> const& proof, 
                           std::ostream& out);

        unsigned get_verified_count() const { return m_verified_count; }
        unsigned get_skipped_count() const { return m_skipped_count; }

        bool conflict_analysis(literal_vector const& cl, clause* cp);
        bool conflict_analysis(literal_vector const& cl, clause* cp, proof_visitor& v);
        void traceLevel0(proof_visitor& v, unsigned start = 0);
        void traverseLevel0(proof_visitor& v, unsigned start = 0) { traceLevel0(v, start); }

    };
}
