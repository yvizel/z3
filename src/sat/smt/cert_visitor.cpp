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
            expr_ref J = euf_interpolant(clause, &m_steps[sid].euf);
            if (!J)
                fail("certificate: theory lemma " + std::to_string(id) + " has no EUF partial interpolant (generic fallback used)");
            else if (!m_steps[sid].euf.ok)
                IF_VERBOSE(1, verbose_stream() << "certificate: theory lemma " << id << " without EUF certificate: " << m_steps[sid].euf.error << "\n");
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

    // SMT-LIB text of a term. Applications of uninterpreted symbols, which is
    // all that certificates contain, are printed directly and memoized per
    // sub-term: the general pretty printer takes milliseconds on the deeply
    // nested terms of some lemmas, and the same terms are printed many times.
    std::string cert_visitor::term(expr* e) {
        std::string r;
        if (m_term_text.find(e, r))
            return r;
        if (is_app(e) && to_app(e)->get_family_id() == null_family_id) {
            app* a = to_app(e);
            symbol const& nm = a->get_decl()->get_name();
            std::string name = is_smt2_quoted_symbol(nm) ? mk_smt2_quoted_symbol(nm) : nm.str();
            if (a->get_num_args() == 0)
                r = name;
            else {
                r = "(" + name;
                for (expr* arg : *a) {
                    r += " ";
                    r += term(arg);
                }
                r += ")";
            }
        }
        else {
            params_ref p;
            p.set_uint("min_alias_size", UINT_MAX);
            p.set_uint("max_depth", UINT_MAX);
            p.set_bool("single_line", true);
            std::ostringstream o;
            o << mk_ismt2_pp(e, m, p);
            r = o.str();
        }
        m_term_text.insert(e, r);
        return r;
    }

    void cert_visitor::json_lits(std::ostream& out, literal_vector const& lits) {
        out << "[";
        for (unsigned i = 0; i < lits.size(); ++i) {
            if (i > 0) out << ", ";
            out << json_lit(lits[i]);
        }
        out << "]";
    }

    // The euf object of a theory leaf; atom indices of the certificate are
    // indices into the lemma's clause (euf_interpolant builds one atom per
    // clause literal, in order).
    void cert_visitor::json_euf(std::ostream& out, euf_interpolator::cert const& c, literal_vector const& clause) {
        typedef euf_interpolator::cert cert;
        auto lit_of_atom = [&](unsigned a) { return json_lit(clause[a]); };
        // Only the runs the conflict depends on are exported, renumbered in
        // order. A run that nothing refers to contributes nothing to the
        // exchange proof, and its conclusion need not be a sub-term of the
        // lemma's interpolant, so its terms may no longer exist by now.
        bool_vector live(c.runs.size(), false);
        unsigned_vector todo;
        for (unsigned id : c.final.premises) todo.push_back(id);
        while (!todo.empty()) {
            unsigned id = todo.back();
            todo.pop_back();
            if (id >= c.runs.size() || live[id]) continue;
            live[id] = true;
            for (unsigned p : c.runs[id].premises) todo.push_back(p);
        }
        unsigned_vector new_id(c.runs.size(), UINT_MAX);
        unsigned num_live = 0;
        for (unsigned i = 0; i < c.runs.size(); ++i)
            if (live[i]) new_id[i] = num_live++;
        auto rid = [&](unsigned id) { return id < new_id.size() ? new_id[id] : id; };
        auto run = [&](cert::run const& r, bool with_header, unsigned id) {
            out << "{";
            if (with_header)
                out << "\"id\": " << id << ", \"side\": \"" << (r.side_a ? "A" : "B") << "\", \"lhs\": "
                    << "" , json_string(out, term(r.lhs)), out << ", \"rhs\": ", json_string(out, term(r.rhs)), out << ", ";
            out << "\"premises\": [";
            for (unsigned i = 0; i < r.premises.size(); ++i) { if (i) out << ", "; out << rid(r.premises[i]); }
            out << "], \"steps\": [";
            for (unsigned i = 0; i < r.steps.size(); ++i) {
                cert::step const& st = r.steps[i];
                if (i) out << ", ";
                switch (st.kind) {
                case cert::rule::refl:       out << "{\"rule\": \"refl\", \"term\": "; json_string(out, term(st.term)); out << "}"; break;
                case cert::rule::assumption: out << "{\"rule\": \"assumption\", \"lit\": " << lit_of_atom(st.atom) << "}"; break;
                case cert::rule::premise:    out << "{\"rule\": \"premise\", \"run\": " << rid(st.run) << "}"; break;
                case cert::rule::symm:       out << "{\"rule\": \"symm\", \"of\": " << st.first << "}"; break;
                case cert::rule::trans:      out << "{\"rule\": \"trans\", \"first\": " << st.first << ", \"second\": " << st.second << "}"; break;
                case cert::rule::congr:
                    out << "{\"rule\": \"congr\", \"function\": ";
                    json_string(out, st.f->get_name().str());
                    out << ", \"args\": [";
                    for (unsigned k = 0; k < st.args.size(); ++k) { if (k) out << ", "; out << st.args[k]; }
                    out << "]}";
                    break;
                }
            }
            out << "]}";
        };
        out << "{\"conflict_side\": \"" << (c.conflict_side_a ? "A" : "B") << "\", \"disequality\": " << lit_of_atom(c.diseq_atom)
            << ", \"runs\": [";
        bool first_run = true;
        for (unsigned i = 0; i < c.runs.size(); ++i) {
            if (!live[i]) continue;
            if (!first_run) out << ", ";
            first_run = false;
            out << "\n        ";
            run(c.runs[i], true, new_id[i]);
        }
        out << "], \"final\": ";
        run(c.final, false, 0);
        out << "}";
    }

    // Formulas are exported as a DAG (certificate format version 2): every
    // distinct expression is one entry of the top-level "nodes" array, whose
    // sub-formulas are {"ref": j} with j smaller than the entry's own index.
    // Partial interpolants are hash-consed and heavily shared, so writing
    // them as trees is exponential. The traversal is iterative: chains of
    // conjunctions can be tens of thousands deep.
    unsigned cert_visitor::node_id(expr* root) {
        unsigned id = 0;
        if (m_node_id.find(root, id))
            return id;
        ptr_vector<expr> todo;
        todo.push_back(root);
        ptr_buffer<expr> kids;
        while (!todo.empty()) {
            expr* e = todo.back();
            if (m_node_id.contains(e)) {
                todo.pop_back();
                continue;
            }
            expr* a = nullptr, * b = nullptr;
            char const* op = nullptr;
            kids.reset();
            bool is_atom = false;
            if (m.is_true(e) || m.is_false(e)) {
            }
            else if (m.is_not(e, a)) {
                op = "not";
                kids.push_back(a);
            }
            else if (m.is_and(e) || m.is_or(e)) {
                op = m.is_and(e) ? "and" : "or";
                for (expr* arg : *to_app(e))
                    kids.push_back(arg);
            }
            else if (m.is_implies(e, a, b)) {
                op = "implies";
                kids.push_back(a);
                kids.push_back(b);
            }
            else if (m.is_eq(e, a, b) && !m.is_bool(a)) {
                is_atom = true;
            }
            else if (m.is_eq(e, a, b)) {
                op = "iff";
                kids.push_back(a);
                kids.push_back(b);
            }
            else {
                std::ostringstream o;
                o << "certificate: unsupported formula node " << mk_pp(e, m);
                fail(o.str());
            }
            bool ready = true;
            for (expr* k : kids) {
                if (!m_node_id.contains(k)) {
                    todo.push_back(k);
                    ready = false;
                }
            }
            if (!ready)
                continue;
            todo.pop_back();
            std::ostream& out = m_nodes;
            if (m_num_nodes > 0)
                out << ",";
            out << "\n    ";
            if (m.is_true(e))
                out << "true";
            else if (m.is_false(e))
                out << "false";
            else if (is_atom) {
                out << "{\"eq\": [";
                json_string(out, term(a));
                out << ", ";
                json_string(out, term(b));
                out << "]}";
            }
            else if (!op)
                out << "null";
            else if (kids.size() == 1 && op[0] == 'n')
                out << "{\"not\": {\"ref\": " << m_node_id[kids[0]] << "}}";
            else {
                out << "{\"" << op << "\": [";
                for (unsigned k = 0; k < kids.size(); ++k) {
                    if (k > 0) out << ", ";
                    out << "{\"ref\": " << m_node_id[kids[k]] << "}";
                }
                out << "]}";
            }
            m_node_id.insert(e, m_num_nodes++);
        }
        return m_node_id[root];
    }

    // A formula position: a reference into the node table.
    void cert_visitor::json_formula(std::ostream& out, expr* e) {
        out << "{\"ref\": " << node_id(e) << "}";
    }

    bool cert_visitor::write(std::ostream& out) {
        if (m_labeling != itp_labeling::mcmillan)
            fail("certificate: only the mcmillan labeling is supported");
        if (!m_ab_vars.empty())
            fail("certificate: per-variable ab labels (itp_label_opt) are not supported");

        // Only the atoms the trimmed proof uses are exported (and labeled):
        // the proof log defines many more, e.g. atoms of dropped clauses.
        uint_set used;
        for (step const& s : m_steps) {
            for (literal l : s.lits)
                used.insert(l.var());
            for (literal l : s.pivots)
                used.insert(l.var());
        }

        std::ostringstream body;
        body << "{\n";
        body << "  \"format\": \"euf-itp-certificate\",\n  \"version\": 2,\n";
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
            if (!a || !used.contains(v))
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
        if (has_mixed_atom())
            fail("certificate: the proof uses an atom that mixes A-local and B-local symbols");
        if (has_nonshared_interpolant())
            fail("certificate: a theory lemma's partial interpolant uses a non-shared symbol");
        if (has_uninterpolated_lemma())
            fail("certificate: an EUF lemma has no partial interpolant");

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
                if (s.euf.ok) {
                    body << ", \"euf\": ";
                    json_euf(body, s.euf, s.lits);
                }
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
        body << ",\n";

        if (!m_error.empty())
            return false;
        out << body.str();
        out << "  \"nodes\": [" << m_nodes.str() << "\n  ]\n}\n";
        return true;
    }

}
