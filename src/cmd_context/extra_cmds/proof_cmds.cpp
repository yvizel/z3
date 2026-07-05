/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    proof_cmds.cpp

Abstract:

    Commands for reading and checking proofs.

Author:

    Nikolaj Bjorner (nbjorner) 2022-8-26

Notes:

Proof checker for clauses created during search.
1. Clauses annotated by RUP (reverse unit propagation)
   are checked to be inferrable using reverse unit propagation
   based on previous clauses.
2. Clauses annotated by supported proof rules (proof hints)
   are checked by custom proof checkers. There is a proof checker
   for each proof rule. Main proof checkers just have a single step
   but the framework allows to compose proof rules, each inference
   is checked for correctness by a plugin. 
3. When there are no supported plugin to justify the derived
   clause, or a custom check fails, the fallback is to check that the
   derived clause is a consequence of the input clauses using SMT.
   The last approach is a bail-out and offers a weaker notion of
   self-validation. It is often (but not always) sufficient for using proof
   checking for debugging, as the root-cause for an unsound inference in z3
   does not necessarily manifest when checking the conclusion of the
   inference. An external proof checker that uses such fallbacks could
   use several solvers, or bootstrap from a solver that can generate certificates
   when z3 does not.
   



--*/

#include "util/small_object_allocator.h"
#include "ast/ast_util.h"
#include "ast/ast_ll_pp.h"
#include "ast/arith_decl_plugin.h"
#include "smt/smt_solver.h"
#include "sat/sat_solver.h"
#include "sat/sat_drat.h"
#include "sat/sat_proof_trim.h"
#include "sat/smt/euf_proof_checker.h"
#include "sat/smt/itp_visitor.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/th_rewriter.h"
#include "solver/solver.h"
#include "util/obj_hashtable.h"
#include "cmd_context/cmd_context.h"
#include "params/solver_params.hpp"
#include <iostream>


/**
 * Replay proof entierly, then walk backwards extracting reduced proof.
 */
class proof_trim {
    ast_manager&            m;
    sat::proof_trim         trim;
    euf::theory_checker     m_checker;
    vector<expr_ref_vector> m_clauses;
    bool_vector             m_is_infer;
    u_map<expr*>            m_theory_hints;   // clause id -> theory proof hint (e.g. EUF)
    expr_ref_vector         m_A;              // A-partition input clauses (for interpolant validity checking)
    expr_ref_vector         m_B;              // B-partition input clauses
    symbol                  m_rup;
    bool                    m_empty = false;
    bool                    m_replay = false;
    bool                    m_check_interpolant = false;
    
    void mk_clause(expr_ref_vector const& clause) {
        trim.init_clause();
        for (expr* arg: clause)
            add_literal(arg);
    }
        
    sat::bool_var mk_var(expr* arg) {
        while (arg->get_id() >= trim.num_vars())
            trim.mk_var();
        return arg->get_id();
    }
        
    void add_literal(expr* arg) {
        bool sign = m.is_not(arg, arg);
        trim.add_literal(mk_var(arg), sign);
    }

    bool is_rup(expr* hint) const {
        return hint && is_app(hint) && to_app(hint)->get_decl()->get_name() == m_rup;
    }
      
public:
    proof_trim(cmd_context& ctx):
        // ctx(ctx),
        m(ctx.m()),
        trim(gparams::get_module("sat"), m.limit()),
        m_checker(m),
        m_A(m),
        m_B(m) {
        m_rup = symbol("rup");
    }

    void assume(expr_ref_vector const& clause, sat::ab_mark mark = sat::MARK_NONE) {
        mk_clause(clause);
        trim.assume(m_clauses.size(), true, mark);
        m_clauses.push_back(clause);
        m_is_infer.push_back(false);
        // Track A/B input clauses for interpolant validity checking.
        if (mark == sat::MARK_A)
            m_A.push_back(mk_or(clause));
        else if (mark == sat::MARK_B)
            m_B.push_back(mk_or(clause));
    }

    void set_interpolate(bool b) {
        trim.set_interpolate(b);
    }

    void set_check_interpolant(bool b) {
        m_check_interpolant = b;
    }

    void set_core_first_bcp(bool b) {
        trim.set_core_first_bcp(b);
    }

    void set_reorder(bool b) {
        trim.set_reorder(b);
    }
    
    void del(expr_ref_vector const& _clause) {
        mk_clause(_clause);
        trim.del();
    }

    /**
     * Theory axioms are treated as assumptions.
     * Some literals in the theory axioms may have been removed
     * because they are false at base level. To reconstruct this
     * dependency rely on the proof_checker to produce the original
     * clauses. Thus, trim isn't correct for theory axioms that don't
     * have a way to return clauses.
     * The clauses can be retrieved directly from the justification
     * that is used internally, so adding clause retrieval for every
     * theory axiom is possible even if there are no checkers.
     * In this case, the proof_checker::check dependency should not
     * be used.
     */
    
    void infer(expr_ref_vector const& clause, app* hint, sat::ab_mark mark = sat::MARK_NONE) {
        if (m_empty)
            return;

        if (hint && !is_rup(hint)) {
            auto clause1 = m_checker.clause(hint);
            if (clause1.size() != clause.size()) {
                mk_clause(clause1);
                clause1.push_back(hint);
                unsigned id = m_clauses.size();
                trim.assume(id, true, mark);
                m_theory_hints.insert(id, hint);  // theory lemma
                m_clauses.push_back(clause1);
                m_is_infer.push_back(true);

                if (clause.empty()) {
                    mk_clause(clause);
                    trim.infer(m_clauses.size());
                    m_clauses.push_back(clause);
                    m_clauses.back().push_back(hint);
                    m_is_infer.push_back(true);
                    m_empty = true;
                    do_trim(std::cout, m_replay);
                }
                return;
            }
        }


        mk_clause(clause);
        unsigned id = m_clauses.size();
        if (is_rup(hint))
            trim.infer(id);
        else {
            trim.assume(id, true, mark);
            if (hint)
                m_theory_hints.insert(id, hint);  // theory lemma
        }
        m_clauses.push_back(clause);
        if (hint)
            m_clauses.back().push_back(hint);
        m_is_infer.push_back(true);
        if (clause.empty()) {
            m_empty = true;
            do_trim(std::cout, m_replay);
        }
    }
    
    void updt_params(params_ref const& p) {
        trim.updt_params(p);
    }

    void set_replay(bool replay) {
        m_replay = replay;
    }

    expr_ref mk_dep(unsigned id, unsigned_vector const& deps) {
        arith_util a(m);
        expr_ref_vector args(m);
        args.push_back(a.mk_int(id));
        for (auto d : deps)
            args.push_back(a.mk_int(d));
        return expr_ref(m.mk_app(symbol("deps"), args.size(), args.data(), m.mk_proof_sort()), m);
    }

    // Collect the uninterpreted function/constant symbols occurring in e.
    void collect_ufuncs(expr* e, obj_hashtable<func_decl>& fns) {
        ptr_vector<expr> todo;
        obj_hashtable<expr> seen;
        todo.push_back(e);
        while (!todo.empty()) {
            expr* c = todo.back();
            todo.pop_back();
            if (seen.contains(c))
                continue;
            seen.insert(c);
            if (!is_app(c))
                continue;
            app* a = to_app(c);
            if (a->get_family_id() == null_family_id)
                fns.insert(a->get_decl());
            for (expr* arg : *a)
                todo.push_back(arg);
        }
    }

    // Verify the computed interpolant I for the (A, B) pair:
    //   (1) A => I, (2) I /\ B is unsatisfiable, (3) I uses only shared symbols.
    void check_interpolant(expr* itp, std::ostream& out) {
        expr_ref A(mk_and(m_A), m);
        expr_ref B(mk_and(m_B), m);
        params_ref p;

        // (1) A => I, i.e. A /\ not I is unsatisfiable.
        {
            solver_ref s = mk_smt_solver(m, p, symbol::null);
            s->assert_expr(A);
            s->assert_expr(m.mk_not(itp));
            lbool r = s->check_sat();
            out << "; check A => interpolant: "
                << (r == l_false ? "passed" : r == l_true ? "FAILED (A does not imply interpolant)" : "unknown") << "\n";
        }

        // (2) I /\ B is unsatisfiable.
        {
            solver_ref s = mk_smt_solver(m, p, symbol::null);
            s->assert_expr(B);
            s->assert_expr(itp);
            lbool r = s->check_sat();
            out << "; check interpolant /\\ B unsat: "
                << (r == l_false ? "passed" : r == l_true ? "FAILED (interpolant consistent with B)" : "unknown") << "\n";
        }

        // (3) interpolant only uses symbols shared by A and B.
        {
            obj_hashtable<func_decl> fa, fb, fi;
            for (expr* cl : m_A) collect_ufuncs(cl, fa);
            for (expr* cl : m_B) collect_ufuncs(cl, fb);
            collect_ufuncs(itp, fi);
            bool ok = true;
            for (func_decl* f : fi) {
                if (!fa.contains(f) || !fb.contains(f)) {
                    ok = false;
                    out << ";   interpolant uses non-shared symbol " << f->get_name() << "\n";
                }
            }
            out << "; check interpolant shared symbols only: " << (ok ? "passed" : "FAILED") << "\n";
        }
    }

    void do_trim(std::ostream& out, bool replay) {
        ast_pp_util pp(m);
        auto ids = trim.trim();
        out << "; proof trimming complete, " << ids.size() << " clauses in trimmed proof\n";
        if (replay) {
            //trim.replay_proof(ids, out);
            trim.replay_proof_with_validation(ids, out);
        }
        if (trim.interpolate()) {
            sat::itp_visitor itp(m);
            // Provide the real boolean atoms (bool_var == atom id) so that term/symbol
            // coloring is over the actual EUF terms.
            for (auto const& clause : m_clauses)
                for (expr* e : clause)
                    if (m.is_bool(e)) {
                        expr* atom = e;
                        m.is_not(atom, atom);
                        itp.set_atom(atom->get_id(), atom);
                    }
            for (auto const& kv : m_theory_hints)
                itp.register_theory_clause(kv.m_key, kv.m_value);
            trim.replay_with_visitor(ids, itp, out);
            expr_ref interpolant = itp.get_interpolant();
            IF_VERBOSE(1, if (interpolant) verbose_stream() << "; raw interpolant (" << get_num_exprs(interpolant) << " nodes): " << mk_pp(interpolant, m) << "\n");
            // Simplify the interpolant expression before reporting it.
            if (interpolant) {
                th_rewriter rw(m);
                expr_ref simplified(m);
                rw(interpolant, simplified);
                interpolant = simplified;
            }
            out << "; interpolant: " << mk_pp(interpolant, m) << "\n";
            if (m_check_interpolant && interpolant)
                check_interpolant(interpolant, out);
        }
        for (auto const& [id, deps] : ids) {
            auto& clause = m_clauses[id];
            bool is_infer = m_is_infer[id];
            clause.push_back(mk_dep(id, deps));            
            for (expr* e : clause) 
                pp.collect(e);
            
            pp.display_decls(out);
            for (expr* e : clause) {
                m.is_not(e, e);
                pp.define_expr(out, e);
            }

            if (!is_infer)
                out << "(assume";
            else
                out << "(infer";
            for (expr* e : clause) {
                if (m.is_not(e, e))
                    pp.display_expr_def(out << " (not ", e) << ")";
                else
                    pp.display_expr_def(out << " ", e);
            }
            out << ")\n";
        }
    }

    
};

class proof_saver {
    cmd_context& ctx;
    ast_manager& m;
public:
    proof_saver(cmd_context& ctx):ctx(ctx), m(ctx.m()) {
        auto* s = ctx.get_solver();
        if (!s)
            ctx.set_solver_factory(mk_smt_strategic_solver_factory());
        if (!ctx.get_check_sat_result())
            ctx.set_check_sat_result(ctx.get_solver());
    }

    void assume(expr_ref_vector const& clause) {
        ctx.get_solver()->log_inference(m.mk_assumption_add(nullptr, mk_or(clause)));
    }

    void del(expr_ref_vector const& clause) {
        ctx.get_solver()->log_inference(m.mk_redundant_del(mk_or(clause)));
    }

    void infer(expr_ref_vector const& clause, app* hint) {
        ctx.get_solver()->log_inference(m.mk_lemma_add(hint, mk_or(clause)));
    }
    
};

class proof_cmds_imp : public proof_cmds {
    cmd_context&    ctx;
    ast_manager&    m;
    arith_util      m_arith;
    expr_ref_vector m_lits;
    app_ref         m_proof_hint;
    unsigned_vector m_deps;
    bool            m_check  = true;
    bool            m_save   = false;
    bool            m_trim   = false;
    bool            m_replay = false;
    bool            m_interpolate = false;
    sat::ab_mark    m_mark   = sat::MARK_NONE;
    scoped_ptr<euf::smt_proof_checker>     m_checker;
    scoped_ptr<proof_saver>     m_saver;
    scoped_ptr<proof_trim>      m_trimmer;
    user_propagator::on_clause_eh_t  m_on_clause_eh;
    void*                            m_on_clause_ctx = nullptr;
    expr_ref m_assumption, m_del;
    
    euf::smt_proof_checker& checker() { params_ref p; if (!m_checker) m_checker = alloc(euf::smt_proof_checker, m, p); return *m_checker; }
    proof_saver& saver() { if (!m_saver) m_saver = alloc(proof_saver, ctx); return *m_saver; }
    proof_trim& trim() { if (!m_trimmer) m_trimmer = alloc(proof_trim, ctx); return *m_trimmer; }

    expr_ref assumption() {
        if (!m_assumption)
            m_assumption = m.mk_app(symbol("assumption"), 0, nullptr, m.mk_proof_sort());
        return m_assumption;
    }

    expr_ref del() {
        if (!m_del)
            m_del = m.mk_app(symbol("del"), 0, nullptr, m.mk_proof_sort());
        return m_del;
    }

    bool is_dep(expr* e) {
        return m.is_proof(e) && symbol("deps") == to_app(e)->get_name();
    }

    // A/B partition mark for interpolation, encoded as a nullary proof app
    // __itp_A or __itp_B.
    bool is_mark(expr* e, sat::ab_mark& mark) {
        if (!m.is_proof(e) || !is_app(e))
            return false;
        symbol const& n = to_app(e)->get_name();
        if (n == symbol("__itp_A")) { mark = sat::MARK_A; return true; }
        if (n == symbol("__itp_B")) { mark = sat::MARK_B; return true; }
        return false;
    }

    void get_deps(expr* e) {
        rational n;
        bool is_int = false;
        for (expr* arg : *to_app(e)) 
            if (m_arith.is_numeral(arg, n, is_int) && n.is_unsigned())
                m_deps.push_back(n.get_unsigned());
    }
    
public:
    proof_cmds_imp(cmd_context& ctx): 
        ctx(ctx), 
        m(ctx.m()),
        m_arith(m),
        m_lits(m), 
        m_proof_hint(m), 
        m_assumption(m), 
        m_del(m) {
        updt_params(gparams::get_module("solver"));
    }

    void add_literal(expr* e) override {
        if (m.is_proof(e)) {
            sat::ab_mark mark;
            if (is_dep(e))
                get_deps(e);
            else if (is_mark(e, mark))
                m_mark = mark;
            else if (!m_proof_hint)
                m_proof_hint = to_app(e);
        }
        else if (!m.is_bool(e))
            throw default_exception("literal should be either a Proof or Bool");
        else
            m_lits.push_back(e);
    }

    void end_assumption() override {
        if (m_check)
            checker().assume(m_lits);
        if (m_save)
            saver().assume(m_lits);
        if (m_trim)
            trim().assume(m_lits, m_mark);
        if (m_on_clause_eh)
            m_on_clause_eh(m_on_clause_ctx, assumption(), m_deps.size(), m_deps.data(), m_lits.size(), m_lits.data());
        m_lits.reset();
        m_proof_hint.reset();
        m_deps.reset();
        m_mark = sat::MARK_NONE;
    }

    void end_infer() override {
        if (m_check)
            checker().infer(m_lits, m_proof_hint);
        if (m_save)
            saver().infer(m_lits, m_proof_hint);
        if (m_trim)
            trim().infer(m_lits, m_proof_hint, m_mark);
        if (m_on_clause_eh)
            m_on_clause_eh(m_on_clause_ctx, m_proof_hint, m_deps.size(), m_deps.data(), m_lits.size(), m_lits.data());
        m_lits.reset();
        m_proof_hint.reset();
        m_deps.reset();
        m_mark = sat::MARK_NONE;
    }

    void end_deleted() override {
        if (m_check)
            checker().del(m_lits);
        if (m_save)
            saver().del(m_lits);
        if (m_trim)
            trim().del(m_lits);
        if (m_on_clause_eh)
            m_on_clause_eh(m_on_clause_ctx, del(), m_deps.size(), m_deps.data(), m_lits.size(), m_lits.data());
        m_lits.reset();
        m_proof_hint.reset();
        m_deps.reset();
        m_mark = sat::MARK_NONE;
    }

    void updt_params(params_ref const& p) override {
        solver_params sp(p);
        m_save  = sp.proof_save();
        m_trim  = sp.proof_trim();
        m_replay = sp.proof_replay();
        m_interpolate = sp.proof_interpolate();
        m_check = sp.proof_check() && !m_trim && !m_save && !m_on_clause_eh;
        if (m_trim) {
            trim().updt_params(p);
            trim().set_replay(m_replay);
            trim().set_interpolate(m_interpolate);
            trim().set_check_interpolant(sp.proof_check_interpolant());
            trim().set_core_first_bcp(sp.proof_core_first_bcp());
            trim().set_reorder(sp.proof_reorder());
        }
    }

    void register_on_clause(void* ctx, user_propagator::on_clause_eh_t& on_clause_eh) override {
        m_on_clause_ctx = ctx;
        m_on_clause_eh = on_clause_eh;
        if (m_on_clause_eh)
            m_check = false;
    }

};


static proof_cmds& get(cmd_context& ctx) {
    if (!ctx.get_proof_cmds())
        ctx.set_proof_cmds(alloc(proof_cmds_imp, ctx));
    return *ctx.get_proof_cmds();
}

// assumption
class assume_cmd : public cmd {
public:
    assume_cmd():cmd("assume") {}
    char const* get_usage() const override { return "<expr>+"; }
    char const * get_descr(cmd_context& ctx) const override { return "proof command for adding assumption (input assertion)"; }
    unsigned get_arity() const override { return VAR_ARITY; }
    void prepare(cmd_context & ctx) override {}
    void finalize(cmd_context & ctx) override {}
    void failure_cleanup(cmd_context & ctx) override {}
    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override { return CPK_EXPR; }    
    void set_next_arg(cmd_context & ctx, expr * arg) override { get(ctx).add_literal(arg); }
    void execute(cmd_context& ctx) override { get(ctx).end_assumption(); }
};

// deleted clause
class del_cmd : public cmd {
public:
    del_cmd():cmd("del") {}
    char const* get_usage() const override { return "<expr>+"; }
    char const * get_descr(cmd_context& ctx) const override { return "proof command for clause deletion"; }
    unsigned get_arity() const override { return VAR_ARITY; }
    void prepare(cmd_context & ctx) override {}
    void finalize(cmd_context & ctx) override {}
    void failure_cleanup(cmd_context & ctx) override {}
    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override { return CPK_EXPR; }    
    void set_next_arg(cmd_context & ctx, expr * arg) override { get(ctx).add_literal(arg); }
    void execute(cmd_context& ctx) override { get(ctx).end_deleted(); }
};

// learned/redundant clause
class infer_cmd : public cmd {
public:
    infer_cmd():cmd("infer") {}
    char const* get_usage() const override { return "<expr>+"; }
    char const* get_descr(cmd_context& ctx) const override { return "proof command for learned (redundant) clauses"; }
    unsigned get_arity() const override { return VAR_ARITY; }
    void prepare(cmd_context & ctx) override {}
    void finalize(cmd_context & ctx) override {}
    void failure_cleanup(cmd_context & ctx) override {}
    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override { return CPK_EXPR; }    
    void set_next_arg(cmd_context & ctx, expr * arg) override { get(ctx).add_literal(arg); }
    void execute(cmd_context& ctx) override { get(ctx).end_infer(); }
};

void install_proof_cmds(cmd_context & ctx) {
    ctx.insert(alloc(del_cmd));
    ctx.insert(alloc(infer_cmd));
    ctx.insert(alloc(assume_cmd));
}

void init_proof_cmds(cmd_context& ctx) {
    get(ctx);
}
