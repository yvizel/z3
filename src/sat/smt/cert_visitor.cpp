/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    cert_visitor.cpp

Abstract:

    Implementation of the interpolation-certificate exporting visitor.

Author:

    Yakir Vizel 2025

--*/
#include "sat/smt/cert_visitor.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_pp.h"
#include "util/warning.h"

namespace sat {

    void cert_visitor::fail(std::string const& msg) {
        if (m_error.empty())
            m_error = msg;
    }

    unsigned cert_visitor::unit_id(literal l) {
        bool_var v = l.var();
        if (v < m_unit_id.size() && m_unit_id[v] != UINT_MAX) {
            if (m_unit_lit[v] == l)
                return m_unit_id[v];
            std::ostringstream o;
            o << "certificate: unit clause of variable " << v << " is " << m_unit_lit[v] << ", but " << l << " was required";
            fail(o.str());
            return UINT_MAX;
        }
        std::ostringstream o;
        o << "certificate: missing unit clause for literal " << l;
        fail(o.str());
        return UINT_MAX;
    }

    unsigned cert_visitor::clause_id(literal_vector const& lits) {
        literal_vector key(lits);
        normalize(key);
        unsigned id;
        if (m_clause_id.find(key, id))
            return id;
        if (key.size() == 1)
            return unit_id(key[0]);
        std::ostringstream o;
        o << "certificate: missing id for clause " << key;
        fail(o.str());
        return UINT_MAX;
    }

    unsigned cert_visitor::new_step(literal_vector const& lits, char const* kind, ab_mark mark) {
        step s;
        s.id = m_steps.size();
        s.lits = lits;
        s.kind = kind;
        s.mark = mark;
        m_steps.push_back(s);
        literal_vector key(lits);
        normalize(key);
        m_clause_id.insert(key, s.id);
        if (key.size() == 1) {
            bool_var v = key[0].var();
            m_unit_id.reserve(v + 1, UINT_MAX);
            m_unit_lit.reserve(v + 1, null_literal);
            m_unit_id[v] = s.id;
            m_unit_lit[v] = key[0];
        }
        return s.id;
    }

    void cert_visitor::visit_assumption(unsigned id, literal_vector const& clause, ab_mark mark) {
        itp_visitor::visit_assumption(id, clause, mark);
        bool theory = is_theory(id);
        unsigned sid = new_step(clause, theory ? "theory" : "input", mark);
        if (theory) {
            m_steps[sid].hint = m_theory_hint[id];
            expr_ref J = euf_interpolant(clause);
            if (!J)
                fail("certificate: theory lemma " + std::to_string(id) + " has no EUF partial interpolant (generic fallback used)");
            m_steps[sid].lemma_itp = clause_label(clause);
        }
        else if (mark != MARK_A && mark != MARK_B)
            fail("certificate: input clause " + std::to_string(id) + " without A/B mark");
    }

    // Unit resolvent from the unit premise p1 and the reason p2 (which
    // contains ~p1). In the checker's convention the pivot is the literal of
    // the current clause (the anchor p2), i.e. ~p1.
    int cert_visitor::visitResolvent(literal resolvent, literal p1, proof_clause_ref const& p2) {
        unsigned anchor = clause_id(p2.m_lits);
        unsigned parent = unit_id(p1);
        int r = itp_visitor::visitResolvent(resolvent, p1, p2);
        literal_vector lits;
        lits.push_back(resolvent);
        unsigned sid = new_step(lits, "chain", MARK_NONE);
        m_steps[sid].anchor = anchor;
        m_steps[sid].parents.push_back(parent);
        m_steps[sid].pivots.push_back(~p1);
        return r;
    }

    // Unit derived by a chain: anchor chainClauses[0], then one resolution per
    // pivot against the unit clause of the (true) trail literal chainPivots[i].
    int cert_visitor::visitChainResolvent(literal parent) {
        if (chainClauses.empty())
            return 0;
        unsigned anchor = clause_id(chainClauses[0].m_lits);
        unsigned_vector parents;
        literal_vector pivots;
        for (unsigned i = 0; i < chainPivots.size(); ++i) {
            parents.push_back(unit_id(chainPivots[i]));
            pivots.push_back(~chainPivots[i]);
        }
        int r = itp_visitor::visitChainResolvent(parent);
        literal_vector lits;
        lits.push_back(parent);
        unsigned sid = new_step(lits, "chain", MARK_NONE);
        m_steps[sid].anchor = anchor;
        m_steps[sid].parents = parents;
        m_steps[sid].pivots = pivots;
        return r;
    }

    // Clause (or the empty clause) derived by a chain. chainClauses[i+1] is
    // either a real clause or, when invalid, the unit clause of
    // chainPivots[i].
    int cert_visitor::visitChainResolvent(proof_clause_ref const& parent) {
        if (chainClauses.empty())
            return 0;
        unsigned anchor = clause_id(chainClauses[0].m_lits);
        unsigned_vector parents;
        literal_vector pivots;
        for (unsigned i = 0; i + 1 < chainClauses.size(); ++i) {
            proof_clause_ref const& r = chainClauses[i + 1];
            parents.push_back(r.is_valid() ? clause_id(r.m_lits) : unit_id(chainPivots[i]));
            pivots.push_back(~chainPivots[i]);
        }
        int r = itp_visitor::visitChainResolvent(parent);
        unsigned sid = new_step(parent.m_lits, "chain", MARK_NONE);
        m_steps[sid].anchor = anchor;
        m_steps[sid].parents = parents;
        m_steps[sid].pivots = pivots;
        return r;
    }

    // ---- serialization -------------------------------------------------

    void cert_visitor::json_string(std::ostream& out, std::string const& s) {
        out << '"';
        for (char c : s) {
            switch (c) {
            case '"': out << "\\\""; break;
            case '\\': out << "\\\\"; break;
            case '\n': out << "\\n"; break;
            case '\t': out << "\\t"; break;
            default: out << c;
            }
        }
        out << '"';
    }

    std::string cert_visitor::term(expr* e) {
        params_ref p;
        p.set_uint("min_alias_size", UINT_MAX);
        p.set_uint("max_depth", UINT_MAX);
        p.set_bool("single_line", true);
        std::ostringstream o;
        o << mk_ismt2_pp(e, m, p);
        return o.str();
    }

    void cert_visitor::json_lits(std::ostream& out, literal_vector const& lits) {
        out << "[";
        for (unsigned i = 0; i < lits.size(); ++i) {
            if (i > 0) out << ", ";
            int v = static_cast<int>(lits[i].var()) + 1;
            out << (lits[i].sign() ? -v : v);
        }
        out << "]";
    }

    // Formula tree over equality atoms.
    void cert_visitor::json_formula(std::ostream& out, expr* e) {
        expr* a = nullptr, *b = nullptr;
        if (m.is_true(e)) { out << "true"; return; }
        if (m.is_false(e)) { out << "false"; return; }
        if (m.is_not(e, a)) { out << "{\"not\": "; json_formula(out, a); out << "}"; return; }
        if (m.is_and(e) || m.is_or(e)) {
            out << (m.is_and(e) ? "{\"and\": [" : "{\"or\": [");
            app* ap = to_app(e);
            for (unsigned i = 0; i < ap->get_num_args(); ++i) {
                if (i > 0) out << ", ";
                json_formula(out, ap->get_arg(i));
            }
            out << "]}";
            return;
        }
        if (m.is_implies(e, a, b)) {
            out << "{\"implies\": [";
            json_formula(out, a); out << ", "; json_formula(out, b);
            out << "]}";
            return;
        }
        if (m.is_eq(e, a, b) && !m.is_bool(a)) {
            out << "{\"eq\": [";
            json_string(out, term(a)); out << ", "; json_string(out, term(b));
            out << "]}";
            return;
        }
        if (m.is_eq(e, a, b) || m.is_iff(e)) {
            app* ap = to_app(e);
            out << "{\"iff\": [";
            json_formula(out, ap->get_arg(0)); out << ", "; json_formula(out, ap->get_arg(1));
            out << "]}";
            return;
        }
        std::ostringstream o;
        o << "certificate: unsupported formula node " << mk_pp(e, m);
        fail(o.str());
        out << "null";
    }

    bool cert_visitor::write(std::ostream& out) {
        if (m_labeling != itp_labeling::mcmillan)
            fail("certificate: only the mcmillan labeling is supported");
        if (!m_ab_vars.empty())
            fail("certificate: per-variable ab labels (itp_label_opt) are not supported");

        std::ostringstream body;
        body << "{\n";
        body << "  \"format\": \"euf-itp-certificate\",\n  \"version\": 1,\n";
        body << "  \"labeling\": \"mcmillan\",\n";

        // symbols with colors
        body << "  \"symbols\": [";
        bool first = true;
        for (auto const& kv : m_sym_mark) {
            if (!first) body << ",";
            first = false;
            body << "\n    {\"name\": ";
            json_string(body, kv.m_key->get_name().str());
            body << ", \"arity\": " << kv.m_key->get_arity()
                 << ", \"color\": \"" << ab_mark_to_string(kv.m_value) << "\"}";
        }
        body << "\n  ],\n";

        // atoms: every variable with an atom must be an equality
        body << "  \"atoms\": [";
        first = true;
        for (unsigned v = 0; v < m_atoms.size(); ++v) {
            expr* a = m_atoms[v];
            if (!a)
                continue;
            expr* l = nullptr, *r = nullptr;
            if (!m.is_eq(a, l, r) || m.is_bool(l)) {
                std::ostringstream o;
                o << "certificate: atom of variable " << v << " is not an equality: " << mk_pp(a, m);
                fail(o.str());
                continue;
            }
            if (!first) body << ",";
            first = false;
            body << "\n    {\"var\": " << (v + 1) << ", \"lhs\": ";
            json_string(body, term(l));
            body << ", \"rhs\": ";
            json_string(body, term(r));
            body << ", \"label\": \"" << (label(v) == lbl::a ? "a" : "b") << "\"}";
        }
        body << "\n  ],\n";

        // steps
        body << "  \"steps\": [";
        for (unsigned i = 0; i < m_steps.size(); ++i) {
            step const& s = m_steps[i];
            if (i > 0) body << ",";
            body << "\n    {\"id\": " << s.id << ", \"kind\": \"" << s.kind << "\", \"lits\": ";
            json_lits(body, s.lits);
            if (s.kind == "input")
                body << ", \"side\": \"" << (s.mark == MARK_A ? "A" : "B") << "\"";
            else if (s.kind == "theory") {
                body << ", \"hint\": ";
                json_string(body, s.hint ? term(s.hint) : "");
                body << ", \"itp\": ";
                if (s.lemma_itp) json_formula(body, s.lemma_itp); else body << "null";
            }
            else {
                body << ", \"anchor\": " << s.anchor << ", \"chain\": [";
                for (unsigned j = 0; j < s.parents.size(); ++j) {
                    if (j > 0) body << ", ";
                    int v = static_cast<int>(s.pivots[j].var()) + 1;
                    body << "{\"parent\": " << s.parents[j] << ", \"pivot\": " << (s.pivots[j].sign() ? -v : v) << "}";
                }
                body << "]";
            }
            body << "}";
        }
        body << "\n  ],\n";

        body << "  \"interpolant\": ";
        if (m_raw_interpolant) json_formula(body, m_raw_interpolant); else body << "null";
        body << "\n}\n";

        if (!m_error.empty())
            return false;
        out << body.str();
        return true;
    }

}
