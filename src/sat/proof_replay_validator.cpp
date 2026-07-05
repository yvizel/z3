/*++
  Copyright (c) 2025 Microsoft Corporation

  Module Name:

    proof_replay_validator.cpp

  Abstract:
    
    Implementation of proof replay validator.

  Author:

    Yakir Vizel 2025

--*/

#include "sat/proof_visitor_impl.h"
#include "sat/proof_replay_validator.h"

namespace sat {

    proof_replay_validator::proof_replay_validator(params_ref const& p, reslimit& lim)
        : s(p, lim), m_verified_count(0), m_skipped_count(0), m_bcp_filter(*this) {
        s.set_trim();
    }

    // Round layout: core-first rounds (if enabled) precede the unrestricted
    // ones, and within each core block the A-only round precedes the
    // any-color round (mirroring MiniSat's propagate(coreOnly, maxPart)
    // nesting: coreOnly outermost, partition innermost). The last round has
    // no restriction, so filtered BCP is deductively complete.
    unsigned proof_replay_validator::bcp_color_filter::num_rounds() const {
        return (v.m_core_first ? 2 : 1) * (v.reorder_enabled() ? 2 : 1);
    }

    bool proof_replay_validator::may_use_clause(ab_mark color, bool core, unsigned round) const {
        unsigned color_rounds = reorder_enabled() ? 2 : 1;
        unsigned idx = round - 1;
        if (m_core_first && idx < color_rounds && !core)
            return false;
        if (reorder_enabled() && idx % color_rounds == 0 && color != MARK_A)
            return false;
        return true;
    }

    bool proof_replay_validator::bcp_color_filter::may_propagate(clause const& c, unsigned round) const {
        unsigned id = c.id();
        ab_mark color = id < v.m_cls_color.size() ? v.m_cls_color[id] : MARK_NONE;
        bool core = id < v.m_cls_core.size() && v.m_cls_core[id];
        return v.may_use_clause(color, core, round);
    }

    bool proof_replay_validator::bcp_color_filter::may_propagate(literal l1, literal l2, unsigned round) const {
        unsigned tag = MARK_NONE;
        v.m_bin_tag.find(bin_key(l1, l2), tag);
        return v.may_use_clause(static_cast<ab_mark>(tag & MARK_AB), (tag & 4) != 0, round);
    }

    void proof_replay_validator::record_clause_tag(clause* cl, literal_vector const& lits, ab_mark color) {
        if (!bcp_filter_active())
            return;
        if (cl) {
            m_cls_color.setx(cl->id(), color, MARK_NONE);
            m_cls_core.setx(cl->id(), false, false);
        }
        else if (lits.size() == 2) {
            // Duplicate binary clauses share one watch-filter entry: any
            // A-marked copy justifies propagating in the A round (the chain
            // references the clause by its literals, and the A copy is that
            // clause), and core status is the union of the copies.
            uint64_t key = bin_key(lits[0], lits[1]);
            unsigned tag = 0;
            if (m_bin_tag.find(key, tag)) {
                ab_mark old_color = static_cast<ab_mark>(tag & MARK_AB);
                color = (color == MARK_A || old_color == MARK_A) ? MARK_A : (old_color | color);
                m_bin_tag.remove(key);
            }
            m_bin_tag.insert(key, color | (tag & 4));
        }
    }

    void proof_replay_validator::set_core_tag(proof_clause_ref const& c) {
        if (!bcp_filter_active())
            return;
        if (c.m_clause)
            m_cls_core.setx(c.m_clause->id(), true, false);
        else if (c.m_lits.size() == 2) {
            uint64_t key = bin_key(c.m_lits[0], c.m_lits[1]);
            unsigned tag = MARK_NONE;
            if (m_bin_tag.find(key, tag))
                m_bin_tag.remove(key);
            m_bin_tag.insert(key, tag | 4);
        }
    }

    void proof_replay_validator::assume(unsigned id, bool is_initial) {
        std::sort(m_clause.begin(), m_clause.end());
        unsigned j = 0;
        sat::literal prev = null_literal;
        for (unsigned i = 0; i < m_clause.size(); ++i)
            if (m_clause[i] != prev)
                prev = m_clause[j++] = m_clause[i];
        m_clause.shrink(j);

        if (unit_or_binary_occurs())
            return;

        if (!m_conflict.empty() && m_clause.empty()) {
            m_clauses.insert(m_clause, { {}, id, false, true });
            m_trail.push_back({ id, m_clause, nullptr, true, is_initial });
        }
        if (!m_conflict.empty())
            return;

        IF_VERBOSE(3, verbose_stream() << (is_initial ? "assume " : "rup ") << m_clause << "\n");

        auto* cl = s.mk_clause(m_clause, status::redundant());
        record_clause_tag(cl, m_clause, clause_color(id));
        auto& [clauses, id2, verified, in_core] = m_clauses.insert_if_not_there(m_clause, { {}, id, false, true });
        if (cl)
            clauses.push_back(cl);
        m_trail.push_back({ id, m_clause, cl, true, is_initial });

        auto is_unit2 = [&]() {
            if (s.value(m_clause[0]) == l_false)
                std::swap(m_clause[0], m_clause[1]);
            return s.value(m_clause[1]) == l_false;
        };

        auto is_unit = [&]() {
            unsigned undef_idx = m_clause.size();
            for (unsigned i = 0; i < m_clause.size(); ++i) {
                sat::literal lit = (*cl)[i];
                if (s.value(lit) != l_undef)
                    continue;
                if (undef_idx < m_clause.size())
                    return false;
                undef_idx = i;
            }
            if (undef_idx < m_clause.size()) {
                std::swap((*cl)[undef_idx], (*cl)[0]);
                return true;
            }
            return false;
        };

        if (all_of(m_clause, [&](sat::literal lit) { return s.value(lit) == l_false; })) {
            IF_VERBOSE(3, verbose_stream() << "false clause " << m_clause << "\n");
            set_solver_conflict(m_clause, cl);
            set_conflict(m_clause, cl);
            return;
        }

        if (m_clause.size() == 2 && is_unit2())
            s.propagate_bin_clause(m_clause[0], m_clause[1]);
        else if (m_clause.size() > 2 && cl && is_unit())
            s.propagate_clause(*cl, true, 0, s.cls_allocator().get_offset(cl));
        s.propagate(false);
        if (s.inconsistent()) {
            IF_VERBOSE(3, verbose_stream() << "conflict " << m_clause << "\n");
            set_conflict(m_clause, cl);
        }
    }

    void proof_replay_validator::infer(unsigned id) {
        noop_proof_visitor v;
        infer(id, v);
    }

    bool proof_replay_validator::infer(unsigned id, proof_visitor& v) {
        bool valid = conflict_analysis(m_clause, nullptr, v);
        if (valid)
            assume(id, false);
        return valid;
    }

    void proof_replay_validator::del() {
        std::sort(m_clause.begin(), m_clause.end());
        clause* cp = del(m_clause);
        m_trail.push_back({ 0, m_clause, cp, false, true });
    }

    void proof_replay_validator::add_dependency(literal lit) {
        if (!m_in_deps.contains(lit.var())) {
            m_in_deps.insert(lit.var());
        }
    }

    void proof_replay_validator::add_dependency(justification j) {
        // TODO: Implement if needed for RUP verification
    }

    void proof_replay_validator::add_verified(bool_var v) {
        if (!m_in_coi.contains(v)) {
            m_in_coi.insert(v);
            
            // TODO: Get justification if needed for RUP verification
            // justification j = s.get_justification(v);
        }
    }

    void proof_replay_validator::add_verified(literal l, justification j) {
        add_verified(l.var());
        add_dependency(j);
    }

    bool proof_replay_validator::in_verified(literal_vector const& cl) const {
        for (literal lit : cl) {
            if (!m_in_coi.contains(lit.var())) {
                return false;
            }
        }
        return true;
    }

    clause* proof_replay_validator::del(literal_vector const& cl) {
        auto& entry = m_clauses.find(cl);
        if (entry.m_clauses.empty()) return nullptr;
        clause* cp = entry.m_clauses.back();
        entry.m_clauses.pop_back();
        return cp;
    }

    void proof_replay_validator::del(literal_vector const& cl, clause* cp) {
        // Delete clause from tracking
        auto& entry = m_clauses.find(cl);
        for (auto it = entry.m_clauses.begin(); it != entry.m_clauses.end(); ++it) {
            if (*it == cp) {
                entry.m_clauses.erase(it);
                break;
            }
        }
    }

    void proof_replay_validator::insert_dep(unsigned dep) {
        m_in_deps.insert(dep);
    }

    bool proof_replay_validator::unit_or_binary_occurs() {
        if (m_clause.size() == 1) {
            literal lit = m_clause[0];
            if (m_units.contains(lit.index())) {
                return true;
            }
            m_units.insert(lit.index());
        }
        return false;
    }

    void proof_replay_validator::normalize_clause(literal_vector& cl) const {
        std::sort(cl.begin(), cl.end());
        unsigned j = 0;
        literal prev = null_literal;
        for (unsigned i = 0; i < cl.size(); ++i)
            if (cl[i] != prev)
                prev = cl[j++] = cl[i];
        cl.shrink(j);
    }

    bool proof_replay_validator::mk_proof_clause(literal consequent, justification js, proof_clause_ref& out) {
        out = proof_clause_ref();
        out.m_valid = true;
        switch (js.get_kind()) {
        case justification::NONE:
            if (consequent != null_literal)
                out.m_lits.push_back(consequent);
            return true;
        case justification::BINARY:
            if (consequent == null_literal)
                return false;
            out.m_lits.push_back(consequent);
            out.m_lits.push_back(js.get_literal());
            return true;
        case justification::CLAUSE: {
            clause& c = s.get_clause(js);
            out.m_clause = &c;
            out.m_lits.append(c.size(), c.begin());
            return true;
        }
        case justification::EXT_JUSTIFICATION:
            return false;
        default:
            UNREACHABLE();
            return false;
        }
    }

    bool proof_replay_validator::should_resolve(literal lit) const {
        bool_var v = lit.var();
        justification js = s.get_justification(v);
        if (js.is_ext_justification())
            return false;
        if (s.lvl(v) == 0)
            return true;
        return v < m_propagated.size() && m_propagated[v] && !js.is_none();
    }

    void proof_replay_validator::mark_core(proof_clause_ref const& c) {
        if (!c.is_valid())
            return;
        set_core_tag(c);
        literal_vector cl;
        cl.append(c.m_lits);
        normalize_clause(cl);
        if (m_clauses.contains(cl))
            m_clauses.find(cl).m_in_core = true;
    }

    unsigned proof_replay_validator::max_level(proof_clause_ref const& c) const {
        unsigned lvl = 0;
        if (!c.is_valid())
            return lvl;
        for (literal lit : c.m_lits)
            lvl = std::max(lvl, s.lvl(lit));
        return lvl;
    }

    bool proof_replay_validator::subsumes(literal_vector const& a, literal_vector const& b) const {
        for (literal lit : a)
            if (!b.contains(lit))
                return false;
        return true;
    }

    void proof_replay_validator::set_solver_conflict(literal_vector const& cl, clause* cp) {
        if (s.inconsistent())
            return;
        if (cl.empty()) {
            s.set_conflict();
            return;
        }
        if (!cp)
            return;

        unsigned lvl = 0;
        for (literal lit : cl)
            lvl = std::max(lvl, s.lvl(lit));
        s.set_conflict(justification(lvl, s.cls_allocator().get_offset(cp)));
    }

    void proof_replay_validator::traceLevel0(proof_visitor& v, unsigned start) {
        traceLevel0(v, start, s.m_trail.size());
    }

    void proof_replay_validator::traceLevel0(proof_visitor& v, unsigned start, unsigned end) {
        if (start > s.m_trail.size())
            return;
        end = std::min(end, s.m_trail.size());
        if (start > end)
            return;

        for (unsigned i = start; i < end; ++i) {
            literal q = s.m_trail[i];
            justification js = s.get_justification(q);
            if (js.is_none())
                continue;

            proof_clause_ref reason;
            if (!mk_proof_clause(q, js, reason)) {
                IF_VERBOSE(3, s.display_justification(verbose_stream() << "skip proof trace for " << q << " ", js) << "\n");
                continue;
            }

            if (reason.m_lits.size() <= 1)
                continue;

            if (js.is_binary_clause()) {
                v.visitResolvent(q, ~js.get_literal(), reason);
                continue;
            }

            if (!js.is_clause())
                continue;

            clause& c = s.get_clause(js);
            if (c.size() == 1)
                continue;

            if (c.size() == 2) {
                if (c[0] != q && c[1] != q) {
                    IF_VERBOSE(3, verbose_stream() << "skip proof trace for " << q << ": consequent is not in " << c << "\n");
                    continue;
                }
                literal other = c[0] == q ? c[1] : c[0];
                v.visitResolvent(q, ~other, reason);
                continue;
            }

            v.chainClauses.reset();
            v.chainPivots.reset();
            v.chainClauses.push_back(reason);

            bool found_consequent = false;
            for (literal lit : c) {
                if (!found_consequent && lit == q) {
                    found_consequent = true;
                    continue;
                }
                v.chainPivots.push_back(~lit);
                v.chainClauses.push_back(proof_clause_ref());
            }
            if (!found_consequent) {
                IF_VERBOSE(3, verbose_stream() << "skip proof trace for " << q << ": consequent is not in " << c << "\n");
                continue;
            }
            v.visitChainResolvent(q);
        }
    }

    // Partition rank of a chain clause: PART_A for pure-A clauses, PART_ALL
    // otherwise. Single-literal refs are unit leaves; their rank is the mark
    // of the unit's level-0 derivation (trail mark), since resolving with a
    // unit stands for splicing in that derivation.
    unsigned proof_replay_validator::part_of(proof_clause_ref const& c) const {
        if (c.m_clause) {
            unsigned id = c.m_clause->id();
            return mark_part(id < m_cls_color.size() ? m_cls_color[id] : MARK_NONE);
        }
        if (c.m_lits.size() == 2) {
            unsigned tag = MARK_NONE;
            m_bin_tag.find(bin_key(c.m_lits[0], c.m_lits[1]), tag);
            return mark_part(static_cast<ab_mark>(tag & MARK_AB));
        }
        if (c.m_lits.size() == 1) {
            bool_var x = c.m_lits[0].var();
            return mark_part(m_trail_colors && x < m_trail_colors->size() ? (*m_trail_colors)[x] : MARK_NONE);
        }
        return PART_ALL;
    }

    // Partition rank of the reason that resolving pivot q would bring into
    // the chain. q may be either occurrence of the variable (chains hold the
    // false occurrence, the trail the true one); the reason justifies the
    // trail literal, whose sign the binary-clause key needs.
    unsigned proof_replay_validator::reason_part(literal q) const {
        literal t = s.value(q) == l_false ? ~q : q;
        justification js = s.get_justification(q.var());
        switch (js.get_kind()) {
        case justification::NONE: {
            bool_var x = q.var();
            return mark_part(m_trail_colors && x < m_trail_colors->size() ? (*m_trail_colors)[x] : MARK_NONE);
        }
        case justification::BINARY: {
            unsigned tag = MARK_NONE;
            m_bin_tag.find(bin_key(t, js.get_literal()), tag);
            return mark_part(static_cast<ab_mark>(tag & MARK_AB));
        }
        case justification::CLAUSE: {
            unsigned id = s.get_clause(js).id();
            return mark_part(id < m_cls_color.size() ? m_cls_color[id] : MARK_NONE);
        }
        default:
            return PART_ALL;
        }
    }

    // MiniSat's fixrec: before a mixed (PART_ALL) chain resolves pivot
    // `consequent` with its pure-A reason, re-derive that reason within
    // partition PART_A only - resolving away those of its literals that have
    // A reasons - and emit the resulting clause as its own single-colored
    // chain. The purified clause replaces the reason in the outer chain, so
    // A sub-derivations are factored out of mixed chains. Cached per
    // variable: the reason of an assigned variable is fixed, so purification
    // is done (and its chain emitted) at most once per assignment.
    proof_clause_ref proof_replay_validator::purify_reason(proof_visitor& v, literal consequent, proof_clause_ref const& reason) {
        unsigned idx;
        if (m_purify_memo.find(consequent.var(), idx))
            return m_purified[idx];

        proof_clause_ref result = reason;
        literal_vector learnt;
        if (traverse_bounded(v, reason, consequent, PART_A, learnt) && !v.chainPivots.empty()) {
            literal_vector a(learnt), b(reason.m_lits);
            normalize_clause(a);
            normalize_clause(b);
            if (a != b) {
                result = proof_clause_ref();
                result.m_valid = true;
                result.m_lits.append(learnt);
                v.visitChainResolvent(result);
            }
        }
        m_purify_memo.insert(consequent.var(), m_purified.size());
        m_purified.push_back(result);
        return result;
    }

    // Conflict analysis bounded to partition `part`: starting from confl0
    // (all of whose literals are false, except consequent0 if given, which
    // is the literal confl0 implies), resolve pivots in reverse trail order,
    // but only those whose reason ranks within `part`; the rest end up in
    // out_learnt. Leaves the chain in v.chainClauses / v.chainPivots.
    bool proof_replay_validator::traverse_bounded(proof_visitor& v, proof_clause_ref const& confl0, literal consequent0, unsigned part, literal_vector& out_learnt) {
        bool_vector seen(num_vars(), false);
        bool_vector learnt_seen(num_vars(), false);
        unsigned pathC = 0;
        literal p = consequent0;
        proof_clause_ref confl = confl0;

        out_learnt.reset();
        if (p != null_literal) {
            // the purified clause still implies the consequent
            out_learnt.push_back(p);
            learnt_seen[p.var()] = true;
        }

        int index = static_cast<int>(s.m_trail.size()) - 1;
        vector<proof_clause_ref> chainClauses;
        literal_vector chainPivots;

        do {
            if (!confl.is_valid())
                return false;

            chainClauses.push_back(confl);
            mark_core(confl);
            if (p != null_literal && chainClauses.size() > 1)
                chainPivots.push_back(p);

            literal_vector const& c = confl.m_lits;
            bool skipped_consequent = p == null_literal;
            for (unsigned j = 0; j < c.size(); ++j) {
                if (!skipped_consequent && c[j] == p) {
                    skipped_consequent = true;
                    continue;
                }
                literal q = c[j];
                bool_var x = q.var();
                if (seen[x])
                    continue;
                if (should_resolve(q) && (!reorder_enabled() || reason_part(q) <= part)) {
                    seen[x] = true;
                    ++pathC;
                }
                else if (!learnt_seen[x]) {
                    learnt_seen[x] = true;
                    out_learnt.push_back(q);
                }
            }
            if (pathC == 0)
                break;

            while (index >= 0 && !seen[s.m_trail[index].var()])
                --index;
            if (index < 0)
                return false;

            p = s.m_trail[index--];
            if (!mk_proof_clause(p, s.get_justification(p), confl))
                return false;
            if (reorder_enabled() && part >= PART_ALL && reason_part(p) == PART_A)
                confl = purify_reason(v, p, confl);
            seen[p.var()] = false;
            --pathC;
        }
        while (true);

        v.chainClauses.reset();
        v.chainPivots.reset();
        for (proof_clause_ref const& c : chainClauses)
            v.chainClauses.push_back(c);
        v.chainPivots.append(chainPivots);

        return true;
    }

    bool proof_replay_validator::traverse(proof_visitor& v, proof_clause_ref const& proof_clause, literal_vector& out_learnt) {
        proof_clause_ref confl;
        literal consequent = s.m_not_l == null_literal ? null_literal : ~s.m_not_l;

        out_learnt.reset();
        if (!mk_proof_clause(consequent, s.m_conflict, confl))
            return false;

        if (!reorder_enabled())
            return traverse_bounded(v, confl, null_literal, PART_ALL, out_learnt);

        // FMCAD'14 proof restructuring: derive the lemma in partition
        // stages. If the conflict is within PART_A, first build a chain over
        // PART_A clauses only; unless that already derives the target lemma,
        // emit the result as an intermediate lemma and continue from it with
        // the partition bound lifted. Chains thus stay single-colored except
        // for one final chain that mixes B clauses with A-derived lemmas.
        unsigned part = part_of(confl);
        while (true) {
            if (!traverse_bounded(v, confl, null_literal, part, out_learnt)) {
                if (part >= PART_ALL)
                    return false;
                part = PART_ALL;
                continue;
            }
            if (part >= PART_ALL)
                return true;

            literal_vector learnt(out_learnt), target(proof_clause.m_lits);
            normalize_clause(learnt);
            normalize_clause(target);
            if (subsumes(learnt, target))
                return true;  // lemma fully derived within partition A

            part = PART_ALL;
            if (v.chainPivots.empty())
                continue;  // nothing was resolved; no intermediate lemma to emit

            // emit the A-stage result and restart the analysis from it
            proof_clause_ref inter;
            inter.m_valid = true;
            inter.m_lits.append(out_learnt);
            v.visitChainResolvent(inter);
            confl = inter;
        }
    }

    bool proof_replay_validator::conflict_analysis(literal_vector const& cl, clause* cp) {
        noop_proof_visitor v;
        return conflict_analysis(cl, cp, v);
    }

    bool proof_replay_validator::conflict_analysis(literal_vector const& cl, clause* cp, proof_visitor& v) {
        (void)cp;

        literal_vector target;
        target.append(cl);
        normalize_clause(target);
        IF_VERBOSE(3, verbose_stream() << "validate " << target << "\n");

        proof_clause_ref proof_clause;
        proof_clause.m_valid = true;
        proof_clause.m_lits.append(target);

        bool res = false;
        bool chain_valid = true;
        unsigned base_trail_size = s.m_trail.size();
        unsigned trail_size0 = base_trail_size;
        bool is_empty_clause = target.empty();
        bool probe = !is_empty_clause && !s.inconsistent();
        m_propagated.resize(num_vars(), false);

        if (probe) {
            SASSERT(!s.inconsistent());
            s.push();
            unsigned lvl = s.scope_lvl();
            for (literal lit : target) {
                s.assign(~lit, justification(lvl));
                if (s.inconsistent())
                    break;
            }
            trail_size0 = s.m_trail.size();
            if (!s.inconsistent())
                s.propagate(false);
            if (!s.inconsistent()) {
                s.m_qhead = 0;
                s.propagate(false);
            }
            if (!s.inconsistent())
                IF_VERBOSE(0, s.display(verbose_stream() << "failed RUP probe on " << target << "\n"));
            for (unsigned i = trail_size0; i < s.m_trail.size(); ++i)
                m_propagated[s.m_trail[i].var()] = true;
        }
        else if (is_empty_clause) {
            if (!s.inconsistent())
                s.propagate(false);
            if (!s.inconsistent()) {
                s.m_qhead = 0;
                s.propagate(false);
            }
            if (!s.inconsistent() && !m_conflict.empty() &&
                all_of(m_conflict, [&](literal lit) { return s.value(lit) == l_false; }))
                set_solver_conflict(m_conflict, m_conflict_clause);
            for (unsigned i = trail_size0; i < s.m_trail.size(); ++i)
                m_propagated[s.m_trail[i].var()] = true;
        }

        res = s.inconsistent();
        if (res) {
            proof_clause_ref conflict_clause;
            literal consequent = s.m_not_l == null_literal ? null_literal : ~s.m_not_l;
            IF_VERBOSE(3, s.display_justification(verbose_stream() << "conflict " << s.m_not_l << " ", s.m_conflict) << "\n");
            IF_VERBOSE(3, s.display(verbose_stream()));

            if (mk_proof_clause(consequent, s.m_conflict, conflict_clause) && max_level(conflict_clause) == 0) {
                unsigned trace_end = is_empty_clause ? s.m_trail.size() : base_trail_size;
                traceLevel0(v, m_trace_start, trace_end);
                m_trace_start = trace_end;
            }

            literal_vector learnt;
            if (traverse(v, proof_clause, learnt)) {
                literal_vector normalized_learnt;
                normalized_learnt.append(learnt);
                normalize_clause(normalized_learnt);
                chain_valid = subsumes(normalized_learnt, target);
                if (chain_valid)
                    v.visitChainResolvent(proof_clause);
                else
                    IF_VERBOSE(0, verbose_stream() << "RUP traversal learned " << normalized_learnt
                               << ", which does not subsume " << target << "\n");
            }
            else {
                chain_valid = false;
            }
        }

        for (unsigned i = s.m_trail.size(); i-- > trail_size0; ) {
            bool_var v = s.m_trail[i].var();
            m_propagated[v] = false;
            // purified reasons of probe-level variables die with the probe scope
            m_purify_memo.remove(v);
            if (s.is_marked(v))
                s.reset_mark(v);
        }
        if (probe)
            s.pop(1);

        return res && chain_valid;
    }

    void proof_replay_validator::replay(vector<std::pair<unsigned, unsigned_vector>> const& proof,
                                        vector<std::tuple<unsigned, literal_vector, clause*, bool, bool>> const& trail,
                                        proof_visitor& v,
                                        std::ostream& out,
                                        bool has_terminal_empty_clause,
                                        unsigned terminal_empty_clause_id,
                                        svector<ab_mark> const& clause_marks,
                                        svector<ab_mark> const& var_marks,
                                        svector<ab_mark> const& trail_marks) {
        out << "; === PROOF REPLAY VALIDATION START ===\n";
        out << "; Replaying " << proof.size() << " clauses\n\n";

        m_verified_count = 0;
        m_skipped_count = 0;
        m_trace_start = 0;

        // Colored BCP and proof restructuring (FMCAD'14): propagate A-marked
        // clauses to fixpoint before B-marked ones, so the reasons recorded
        // on the trail stay single-colored as long as possible, and split
        // the RUP chains handed to the visitor into per-partition stages
        // (see traverse). Only affects this internal replay solver - never
        // live search. No-op when interpolation is disabled (marks empty)
        // and core-first mode is off.
        scoped_bcp_filter _bcp_filter(*this, clause_marks, trail_marks);

        auto clause_mark = [&](unsigned id) {
            return id < clause_marks.size() ? clause_marks[id] : MARK_NONE;
        };

        // Proof ids do not coincide with trail positions: deletions push
        // trail entries without an id, while duplicate units and additions
        // made after a conflict push no trail entry at all. Index the trail
        // by the ids actually stored in it.
        unsigned_vector id2idx;
        for (unsigned i = 0; i < trail.size(); ++i) {
            auto const& [tid, lits, cp, is_add, is_init] = trail[i];
            if (is_add)
                id2idx.setx(tid, i, UINT_MAX);
        }

        v.start_replay();
        v.visit_marks(var_marks, trail_marks);

        for (unsigned proof_idx = 0; proof_idx < proof.size(); ++proof_idx) {
            auto const& [id, deps] = proof[proof_idx];
            if (has_terminal_empty_clause && id == terminal_empty_clause_id && proof_idx + 1 == proof.size()) {
                literal_vector empty_clause;
                init_clause();
                v.visit_inference(id, empty_clause, deps, clause_mark(id));
                bool valid = conflict_analysis(empty_clause, nullptr, v);
                if (valid) {
                    ++m_verified_count;
                    out << "; Empty clause " << id << " verified from current conflict\n";
                }
                else {
                    ++m_skipped_count;
                    out << "; WARNING: Empty clause " << id << " is not in conflict with the replay trail\n";
                }
                continue;
            }

            unsigned idx = id < id2idx.size() ? id2idx[id] : UINT_MAX;
            if (idx == UINT_MAX) {
                out << "; Skipping clause " << id << " (no trail entry)\n";
                ++m_skipped_count;
                continue;
            }

            auto const& [trail_id, clause_lits, clause_ptr, is_add, is_initial] = trail[idx];
            (void)trail_id;
            (void)clause_ptr;

            if (!is_add) {
                v.visit_delete(id);
                continue;
            }

            init_clause();
            for (literal lit : clause_lits)
                add_literal(lit.var(), lit.sign());

            if (deps.empty()) {
                v.visit_assumption(id, clause_lits, clause_mark(id));
                assume(id, is_initial);
                traceLevel0(v, m_trace_start);
                m_trace_start = s.m_trail.size();
                ++m_verified_count;
                out << "; Clause " << id << " (assumption) added\n";
            }
            else {
                v.visit_inference(id, clause_lits, deps, clause_mark(id));
                bool valid = infer(id, v);
                if (!valid) {
                    out << "; WARNING: Clause " << id << " failed RUP replay\n";
                    ++m_skipped_count;
                    continue;
                }
                traceLevel0(v, m_trace_start);
                m_trace_start = s.m_trail.size();
                ++m_verified_count;
                out << "; Clause " << id << " (inference) verified and added\n";
            }

            if (s.inconsistent()) {
                traceLevel0(v, m_trace_start);
                m_trace_start = s.m_trail.size();
            }
        }

        v.end_replay();

        out << "\n; === PROOF REPLAY VALIDATION COMPLETE ===\n";
        out << "; Verified: " << m_verified_count << ", Skipped: " << m_skipped_count << "\n";
    }

    void proof_replay_validator::validate_proof(vector<std::pair<unsigned, unsigned_vector>> const& proof, 
                                                std::ostream& out) {
        out << "; === PROOF REPLAY VALIDATION START ===\n";
        out << "; Validating " << proof.size() << " clauses\n\n";
        
        m_verified_count = 0;
        m_skipped_count = 0;

        for (auto const& [id, deps] : proof) {
            if (id >= m_trail.size()) {
                out << "; Skipping clause " << id << " (out of range)\n";
                m_skipped_count++;
                continue;
            }

            auto const& [trail_id, clause_lits, clause_ptr, is_add, is_initial] = m_trail[id];

            // Skip clauses not marked as core
            auto& clause_info = m_clauses.find(clause_lits);
            if (!clause_info.m_in_core) {
                out << "; Skipping clause " << id << " (not in core)\n";
                m_skipped_count++;
                continue;
            }

            if (deps.empty()) {
                // This is an assumption
                out << "; Clause " << id << " (assumption): ";
                for (auto lit : clause_lits)
                    out << lit << " ";
                out << "✓ verified\n";
                m_verified_count++;
            } else {
                // This is an inference
                out << "; Clause " << id << " (inferred from {";
                for (unsigned i = 0; i < deps.size(); ++i) {
                    if (i > 0) out << ", ";
                    out << deps[i];
                }
                out << "}): ";
                for (auto lit : clause_lits)
                    out << lit << " ";

                logging_proof_visitor v(out);
                bool res = conflict_analysis(clause_lits, clause_ptr, v);
                if (res) {
                    out << "✓ verified\n";
                    m_verified_count++;
                } else {
                    out << "✗ failed\n";
                    m_skipped_count++;
                }
            }
        }
        
        out << "\n; === PROOF REPLAY VALIDATION COMPLETE ===\n";
        out << "; Verified: " << m_verified_count << ", Skipped: " << m_skipped_count << "\n";
    }

}
