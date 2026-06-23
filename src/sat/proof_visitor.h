/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    proof_visitor.h

Abstract:

    Visitor interface for proof replay with visitor callbacks.
    
    Supports visitation of proof steps during trimmed proof replay,
    allowing observers to react to each proof generation step.
    
    The visitor pattern enables decoupling of proof processing from proof
    generation, supporting use cases such as:
    - Logging and debugging proof steps
    - Collecting statistics about proofs
    - Validating proof correctness
    - Transforming or optimizing proofs
    - Exporting proofs to external formats

    Usage:
      1. Derive from proof_visitor and implement the virtual methods
      2. Register with EUF solver via set_proof_visitor()
      3. During solving, callbacks are invoked for each proof step
    
    Example:
      class my_visitor : public proof_visitor {
          void visit_assumption(unsigned id, literal_vector const& clause) override {
              // Handle assumption
          }
          // ... implement other methods
      };
      
      my_visitor v;
      euf_solver.set_proof_visitor(&v);

Author:

    Yakir Vizel 2025

--*/
#pragma once

#include "sat/sat_types.h"
#include "sat/sat_clause.h"
#include "sat/proof_mark.h"

namespace sat {

    struct proof_clause_ref {
        literal_vector m_lits;
        clause*        m_clause = nullptr;
        bool           m_valid = false;

        proof_clause_ref() = default;

        proof_clause_ref(unsigned sz, literal const* lits, clause* cp = nullptr):
            m_clause(cp),
            m_valid(true) {
            m_lits.append(sz, lits);
        }

        explicit proof_clause_ref(clause& c):
            proof_clause_ref(c.size(), c.begin(), &c) {
        }

        bool is_valid() const { return m_valid; }
    };

    /**
     * Visitor interface for observing proof steps during replay.
     * 
     * Implementations react to individual proof generation steps,
     * enabling flexible proof processing without modifying the
     * core trimming/replay machinery.
     */
    class proof_visitor {
    public:
        virtual ~proof_visitor() = default;

        /**
         * Called when visiting an assumption (initial) clause during proof replay.
         *
         * \param id - unique identifier for the clause
         * \param clause - literals in the assumption clause
         * \param mark - A/B interpolation mark of the clause (MARK_NONE when
         *               interpolation is disabled)
         */
        virtual void visit_assumption(unsigned id, literal_vector const& clause, ab_mark mark = MARK_NONE) = 0;

        /**
         * Called when visiting an inferred clause during proof replay.
         *
         * Inferred clauses are justified by antecedent clauses.
         *
         * \param id - unique identifier for the clause
         * \param clause - literals in the inferred clause
         * \param antecedents - ids of clause antecedents (premises) for the inference
         * \param mark - A/B interpolation mark of the clause (the union of the
         *               antecedents' marks; MARK_NONE when interpolation is disabled)
         */
        virtual void visit_inference(unsigned id, literal_vector const& clause, unsigned_vector const& antecedents, ab_mark mark = MARK_NONE) = 0;

        /**
         * Called once during replay (after start_replay) to hand the visitor the
         * A/B markings of variables and of the level-0 trail. Both are indexed by
         * bool_var. Empty when interpolation is disabled.
         *
         * \param var_marks   - per-variable marks over original clauses
         * \param trail_marks - per-variable marks of level-0 unit clauses
         */
        virtual void visit_marks(svector<ab_mark> const& var_marks, svector<ab_mark> const& trail_marks) {}

        /**
         * Called when a clause is deleted during proof replay.
         * 
         * Deletions may indicate the clause is no longer needed in the core proof.
         * 
         * \param id - the clause id being deleted
         */
        virtual void visit_delete(unsigned id) = 0;

        /**
         * Called when visiting an external (theory-specific) justification.
         * 
         * Used for justifications from theories like EUF, linear arithmetic, etc.
         * 
         * \param id - the clause id
         * \param theory_id - the theory identifier (family_id or similar)
         * \param info - theory-specific justification information (opaque)
         */
        virtual void visit_external_justification(unsigned id, int theory_id, void* info) = 0;

        /**
         * Called at the start of proof replay.
         * 
         * Visitors can use this to initialize state or prepare logging.
         */
        virtual void start_replay() {}

        /**
         * Called at the end of proof replay.
         * 
         * Visitors can use this to finalize state or report statistics.
         */
        virtual void end_replay() {}

        virtual int visitResolvent(literal, literal, proof_clause_ref const&) { return 0; }
        virtual int visitChainResolvent(literal) { return 0; }
        virtual int visitChainResolvent(proof_clause_ref const&) { return 0; }

        literal_vector            chainPivots;
        vector<proof_clause_ref>  chainClauses;
    };

    /**
     * Default no-op visitor implementation for use as base class.
     * 
     * Provides empty implementations of all virtual methods,
     * allowing derived classes to override only methods they care about.
     */
    class noop_proof_visitor : public proof_visitor {
    public:
        void visit_assumption(unsigned, literal_vector const&, ab_mark = MARK_NONE) override {}
        void visit_inference(unsigned, literal_vector const&, unsigned_vector const&, ab_mark = MARK_NONE) override {}
        void visit_delete(unsigned) override {}
        void visit_external_justification(unsigned, int, void*) override {}
    };

}
