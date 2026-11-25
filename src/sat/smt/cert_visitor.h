/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    cert_visitor.h

Abstract:

    Proof-replay visitor that exports an interpolation certificate.

    The certificate is a JSON file consumed by the Lean checker in
    craig-congruence (`Certify`). It records, in replay order, every clause
    the interpolating visitor (itp_visitor) labels, together with the
    evidence the checker needs to re-derive it without search:

      - input leaves: the literals and the A/B partition;
      - theory leaves: the literals, Z3's proof hint and the partial
        interpolant Z3 computed for the lemma;
      - derived clauses: an LRAT-like resolution chain over earlier
        certificate ids (anchor + ordered (parent, pivot) steps), where the
        pivot is given as the literal occurring in the current resolvent.
        The recorded clause may be a superset of the chain result (Z3 only
        checks subsumption), which the checker treats as weakening.

    Boolean variables are mapped to their atoms (equalities between terms),
    every variable carries its label (a/b) under the chosen labeling, every
    uninterpreted symbol its A/B/AB color, and the raw interpolant of the
    replay is included for the final comparison.

    The visitor derives from itp_visitor so that ids, labels and theory-leaf
    interpolants are exactly the ones the interpolant was computed from.

Author:

    Yakir Vizel 2025

--*/
#pragma once

#include "sat/smt/itp_visitor.h"
#include <sstream>
#include <string>

namespace sat {

    class cert_visitor : public itp_visitor {
        struct step {
            unsigned        id;
            literal_vector  lits;
            std::string     kind;      // "input", "theory", "chain"
            ab_mark         mark = MARK_NONE;
            expr*           hint = nullptr;    // theory leaves
            expr*           lemma_itp = nullptr; // theory leaves: Z3's partial interpolant
            euf_interpolator::cert euf;        // theory leaves: EUF certificate (euf.ok tells if present)
            unsigned        anchor = UINT_MAX; // chains
            unsigned_vector parents;           // chains
            literal_vector  pivots;            // chains: pivot literal as it occurs in the current resolvent
        };

        vector<step>            m_steps;
        // normalized literals of a labeled clause -> certificate id of its most recent derivation
        map<literal_vector, unsigned, lits_hash, lits_eq> m_clause_id;
        unsigned_vector         m_unit_id;     // bool_var -> certificate id of its unit clause (UINT_MAX if none)
        literal_vector          m_unit_lit;    // bool_var -> the literal of that unit clause
        expr_ref                m_raw_interpolant;
        std::string             m_error;

        unsigned clause_id(literal_vector const& lits);
        unsigned unit_id(literal l);
        unsigned new_step(literal_vector const& lits, char const* kind, ab_mark mark);
        void fail(std::string const& msg);

        obj_map<expr, std::string> m_term_text;   // memo of term()
        std::string term(expr* e);
        // formula DAG: expression -> index in the "nodes" array
        obj_map<expr, unsigned> m_node_id;
        std::ostringstream      m_nodes;
        unsigned                m_num_nodes = 0;
        unsigned node_id(expr* e);
        void json_formula(std::ostream& out, expr* e);
        void json_euf(std::ostream& out, euf_interpolator::cert const& c, literal_vector const& clause);
        static int json_lit(literal l) { int v = static_cast<int>(l.var()) + 1; return l.sign() ? -v : v; }
        void json_lits(std::ostream& out, literal_vector const& lits);
        static void json_string(std::ostream& out, std::string const& s);

    public:
        cert_visitor(ast_manager& m): itp_visitor(m), m_raw_interpolant(m) {}

        void set_raw_interpolant(expr* e) { m_raw_interpolant = e; }

        void visit_assumption(unsigned id, literal_vector const& clause, ab_mark mark = MARK_NONE) override;
        int visitResolvent(literal resolvent, literal p1, proof_clause_ref const& p2) override;
        int visitChainResolvent(literal parent) override;
        int visitChainResolvent(proof_clause_ref const& parent) override;

        // Serialize the certificate. Returns false (and reports) if the proof
        // used a feature the certificate format does not cover.
        bool write(std::ostream& out);
        std::string const& error() const { return m_error; }
    };

}
