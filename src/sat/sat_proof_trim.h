/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_trim.h

  Abstract:
   
    proof replay and trim

  Author:

    Nikolaj Bjorner 2023-10-04

  Notes:
  

--*/

#pragma once

#include "util/params.h"
#include "util/statistics.h"
#include "sat/sat_clause.h"
#include "sat/sat_types.h"
#include "sat/sat_solver.h"
#include "sat/proof_mark.h"
#include "sat/proof_replay_validator.h"

namespace sat {

    class proof_trim {
        solver         s;
        literal_vector m_clause, m_clause2, m_conflict;
        uint_set       m_in_deps;
        uint_set       m_in_clause;
        uint_set       m_in_coi;
        clause*        m_conflict_clause = nullptr;
        vector<std::tuple<unsigned, literal_vector, clause*, bool, bool>> m_trail;
        vector<std::pair<unsigned, unsigned_vector>> m_result;
        bool           m_has_terminal_empty_clause = false;
        unsigned       m_terminal_empty_clause_id = 0;
        
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
            bool          m_in_core = false;
            ab_mark       m_mark = MARK_NONE;
        };


        map<literal_vector, clause_info, hash, eq>   m_clauses;
        bool_vector                         m_propagated;

        // A/B markings for interpolation. Populated only when m_interpolate is set.
        bool              m_interpolate = false;
        bool              m_core_first_bcp = false;
        bool              m_reorder = true;
        svector<ab_mark>  m_marks;       // clause id -> mark
        svector<ab_mark>  m_var_mark;    // bool_var -> mark (over original clauses)
        svector<ab_mark>  m_trail_mark;  // bool_var -> mark of its level-0 unit clause

        void del(literal_vector const& cl, clause* cp);

        void prune_trail(literal_vector const& cl, clause* cp);
        void conflict_analysis_core(literal_vector const& cl, clause* cp);
        bool conflict_analysis(literal_vector const& cl, clause* cp);

        void add_dependency(literal lit);
        void add_dependency(justification j);
        void add_core(bool_var v);
        void add_core(literal l, justification j);
        bool in_core(literal_vector const& cl) const;
        void revive(literal_vector const& cl, clause* cp);        
        clause* del(literal_vector const& cl);

        void insert_dep(unsigned dep);

        uint_set m_units;
        bool unit_or_binary_occurs();
        void set_conflict(literal_vector const& c, clause* cp) { m_conflict.reset(); m_conflict.append(c); m_conflict_clause = cp;}
        
    public:

        proof_trim(params_ref const& p, reslimit& lim);

        bool_var mk_var() { return s.mk_var(true, true); }
        void init_clause() { m_clause.reset(); }
        void add_literal(bool_var v, bool sign) { m_clause.push_back(literal(v, sign)); }
        unsigned num_vars() { return s.num_vars(); }

        void assume(unsigned id, bool is_initial = true, ab_mark mark = MARK_NONE);
        void del();
        void infer(unsigned id);
        void updt_params(params_ref const& p) { s.updt_params(p); }

        // Interpolation A/B markings.
        void set_interpolate(bool b) { m_interpolate = b; }
        bool interpolate() const { return m_interpolate; }

        // Prefer core-marked clauses during replay BCP (see
        // proof_replay_validator::set_core_first_bcp).
        void set_core_first_bcp(bool b) { m_core_first_bcp = b; }

        // Colored BCP + chain restructuring during interpolating replay (see
        // proof_replay_validator::set_reorder).
        void set_reorder(bool b) { m_reorder = b; }

        // Compute A/B markings for inferred clauses, variables and the
        // level-0 trail. Must be called after trim() has populated m_result.
        // No-op unless interpolation is enabled.
        void compute_marks();

        ab_mark clause_mark(unsigned id) const { return id < m_marks.size() ? m_marks[id] : MARK_NONE; }
        ab_mark var_mark(bool_var v) const { return v < m_var_mark.size() ? m_var_mark[v] : MARK_NONE; }
        ab_mark trail_mark(literal l) const { return l.var() < m_trail_mark.size() ? m_trail_mark[l.var()] : MARK_NONE; }

        vector<std::pair<unsigned, unsigned_vector>> trim();
        
        void replay_proof(vector<std::pair<unsigned, unsigned_vector>> const& proof, std::ostream& out);
        
        void replay_proof_with_validation(vector<std::pair<unsigned, unsigned_vector>> const& proof, std::ostream& out);

        // Replay the trimmed proof driving a caller-supplied visitor, passing the
        // computed A/B markings. Used e.g. to build an interpolant (itp_visitor).
        void replay_with_visitor(vector<std::pair<unsigned, unsigned_vector>> const& proof, proof_visitor& v, std::ostream& out);

    };
}
