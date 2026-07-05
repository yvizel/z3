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
#include "util/map.h"
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

        // --- proof restructuring (FMCAD'14 "DRUPing for Interpolants") ---
        //
        // RUP chains are built by partition-bounded conflict analysis:
        // clauses are ranked into partitions (PART_A = pure-A clauses,
        // PART_ALL = everything else), and traverse derives each lemma in
        // stages - first a chain restricted to partition PART_A, emitted as
        // an intermediate lemma, then a chain over all clauses. Inside a
        // mixed chain, a pivot whose reason is a pure-A clause first gets
        // that reason "purified" into an A-only-derived clause
        // (purify_reason, cf. MiniSat's fixrec), emitted as its own
        // single-colored chain. Pivots are always resolved in reverse trail
        // order, so chains stay trivial resolution chains. Enabled only
        // during replay() with interpolation marks (m_clause_marks).
        static const unsigned PART_A = 1;
        static const unsigned PART_ALL = 2;
        // bool_var -> mark of its level-0 unit derivation; partition rank of
        // unit leaves in chains.
        svector<ab_mark> const* m_trail_colors = nullptr;
        // bool_var -> index into m_purified: cache of purified reasons, so a
        // reason is purified (and its chain emitted) once per variable
        // assignment. Entries for probe-level variables are dropped when
        // conflict_analysis backtracks.
        u_map<unsigned>          m_purify_memo;
        vector<proof_clause_ref> m_purified;

        bool reorder_enabled() const { return m_clause_marks != nullptr && m_reorder; }
        unsigned mark_part(ab_mark m) const { return m == MARK_A ? PART_A : PART_ALL; }
        unsigned part_of(proof_clause_ref const& c) const;
        unsigned reason_part(literal q) const;
        proof_clause_ref purify_reason(proof_visitor& v, literal consequent, proof_clause_ref const& reason);
        bool traverse_bounded(proof_visitor& v, proof_clause_ref const& confl0, literal consequent0, unsigned part, literal_vector& out_learnt);

        // --- colored / core-first BCP (FMCAD'14 "DRUPing for Interpolants") ---
        //
        // Clause filter installed on the internal replay solver for the
        // duration of a replay() call: propagation runs in rounds, using
        // only A-marked clauses in the first (color) round so that both the
        // reasons recorded on the trail and the resulting RUP chains stay
        // single-colored as long as possible. When core-first mode is on,
        // clauses already marked core (i.e. already used by earlier chains
        // of this replay) get their own leading rounds, biasing new chains
        // towards reusing core clauses. The last round admits every clause,
        // so filtered propagation derives exactly the same assignments as
        // plain BCP.
        class bcp_color_filter : public bcp_filter {
            proof_replay_validator& v;
        public:
            bcp_color_filter(proof_replay_validator& v) : v(v) {}
            unsigned num_rounds() const override;
            bool may_propagate(clause const& c, unsigned round) const override;
            bool may_propagate(literal l1, literal l2, unsigned round) const override;
        };
        friend class bcp_color_filter;

        // proof-clause id -> A/B/AB mark; set for the duration of replay()
        // with interpolation enabled.
        svector<ab_mark> const* m_clause_marks = nullptr;
        bool                    m_core_first = false;
        bool                    m_reorder = true;
        bcp_color_filter        m_bcp_filter;
        // solver clause id -> mark/core tag of the proof clause it was
        // created from; binary clauses have no clause object, so they are
        // keyed by their (order-normalized) pair of literal indices instead.
        svector<ab_mark>        m_cls_color;
        bool_vector             m_cls_core;
        u64_map<unsigned>       m_bin_tag;  // bits 0-1: ab_mark, bit 2: core

        static uint64_t bin_key(literal l1, literal l2) {
            uint64_t a = l1.index(), b = l2.index();
            return a < b ? (a << 32) | b : (b << 32) | a;
        }
        bool bcp_filter_active() const { return reorder_enabled() || m_core_first; }
        ab_mark clause_color(unsigned id) const { return m_clause_marks && id < m_clause_marks->size() ? (*m_clause_marks)[id] : MARK_NONE; }
        void record_clause_tag(clause* cl, literal_vector const& lits, ab_mark color);
        void set_core_tag(proof_clause_ref const& c);
        bool may_use_clause(ab_mark color, bool core, unsigned round) const;

        // Installs the BCP filter on the replay solver for one replay() call
        // and clears it on scope exit, including on exceptions (the mark
        // vectors may be temporaries bound to default arguments, so they
        // must not outlive the call).
        struct scoped_bcp_filter {
            proof_replay_validator& v;
            scoped_bcp_filter(proof_replay_validator& v, svector<ab_mark> const& clause_marks, svector<ab_mark> const& trail_marks) : v(v) {
                v.m_clause_marks = clause_marks.empty() ? nullptr : &clause_marks;
                v.m_trail_colors = trail_marks.empty() ? nullptr : &trail_marks;
                v.m_cls_color.reset();
                v.m_cls_core.reset();
                v.m_bin_tag.reset();
                v.m_purify_memo.reset();
                v.m_purified.reset();
                if (v.bcp_filter_active())
                    v.s.set_bcp_filter(&v.m_bcp_filter);
            }
            ~scoped_bcp_filter() {
                v.s.set_bcp_filter(nullptr);
                v.m_clause_marks = nullptr;
                v.m_trail_colors = nullptr;
            }
        };

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

        // Prefer core-marked clauses during replay BCP: clauses already used
        // by earlier resolution chains propagate in leading rounds, so new
        // chains are biased towards reusing them (cf. MiniSat's
        // propagate(coreOnly) with unrestricted fallback). Never changes
        // which literals get assigned, only the reasons recorded for them.
        void set_core_first_bcp(bool f) { m_core_first = f; }

        // Enable/disable colored BCP and RUP-chain restructuring during
        // interpolating replay (FMCAD'14 proof reordering). On by default;
        // disabling reproduces plain reverse-trail chains, useful to compare
        // interpolants with and without reordering.
        void set_reorder(bool f) { m_reorder = f; }

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
