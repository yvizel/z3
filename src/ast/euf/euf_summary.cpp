/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_summary.cpp

Abstract:

    Summaries for EUF interpolants (IUCs). See euf_summary.h.

Author:

    Isabel Garcia Contreras

--*/

#include "ast/euf/euf_summary.h"

namespace euf {

  static expr_ref rewrite_args(expr * e, const expr_ref_vector &args) {
    ast_manager &m = args.get_manager();
    SASSERT(is_app(e));
    app * a = to_app(e);
    return expr_ref(m.mk_app(a->get_decl(), args.size(), args.data()), m);
  }

  unsigned euf_summarizer::term_color(expr *e) {
    unsigned r;
    if (m_term_color.find(e, r))
      return r;
    r = 3;
    if (is_app(e)) {
      app *a = to_app(e);
      func_decl *f = a->get_decl();
      if (f->get_family_id() == null_family_id) {
        if (!sym_colorable(f)) r &= ~1u;
        if (!sym_shared(f)) r &= ~2u;
      }
      for (expr *arg : *a)
        r &= term_color(arg);
    }
    m_term_color.insert(e, r);
    return r;
  }

  void euf_summarizer::emit(expr_ref_vector const &prem, expr *lhs, expr *rhs) {
    if (lhs == rhs)
      return;
    expr_ref eq(mk_eq_ordered(m, lhs, rhs), m);
    if (prem.empty()) {
      m_sum.push_back(eq);
      return;
    }
    if (prem.contains(eq)) // premise = conclusion: tautology
      return;
    expr_ref body(m);
    body = prem.size() == 1 ? expr_ref(prem.get(0), m) : expr_ref(m.mk_and(prem), m);
    m_sum.push_back(m.mk_implies(body, eq));
  }

  expr_ref euf_summarizer::summarize_branch(enode *n, enode *lca, expr_ref &first_sum,
                                            expr_ref_vector &first_prem, expr_ref_vector &open_prem) {

    expr_ref r(nullptr, m); // beginning of summary
    open_prem.reset();

    if (n == lca)
      return r;

    sum_manager sm(*this, n->get_expr(), first_sum, first_prem);

    while (n != lca) {
      justification &j = n->m_justification;
      if (j.is_congruence()) {
        const congr_sum *csum = nullptr;
        if (!j.is_marked())
          csum = &summarize_congr(n); // marks j if every argument is summarized-side
        else {
          auto it = m_ccsum.find(&j);
          if (it != m_ccsum.end())
            csum = &it->second;
        }
        if (j.is_marked()) {
          // The edge joins the run; nested premises of its arguments travel with it.
          if (!r)
            r = sm.open(expr_ref(n->get_expr(), m));
          if (csum)
            sm.add_premises(csum->prem());
        }
        else {
          switch (csum->mode()) {
          case congr_sum::HORN:
            // The run passes through the edge; the arguments' boundary
            // equalities become premises of the run's clause.
            if (!r)
              r = sm.open(expr_ref(n->get_expr(), m));
            sm.add_premises(csum->prem());
            break;
          case congr_sum::BOUNDARY:
            // Cut the run at the edge: close on the left boundary application
            // and reopen on the right one.
            if (!r)
              r = sm.open(expr_ref(n->get_expr(), m));
            sm.add_premises(csum->left_prem());
            sm.close(rewrite_args(n->get_expr(), csum->left_args()));
            r = sm.open(rewrite_args(n->m_target->get_expr(), csum->right_args()));
            sm.add_premises(csum->right_prem());
            break;
          case congr_sum::ARG_EQS:
          case congr_sum::MARKED:
            // Nothing to do at the edge itself: the arguments' contributions
            // were emitted standalone by summarize_congr.
            break;
          }
        }
      }
      else if (!r && j.is_marked()) { // new summary starts (colorable)
        r = sm.open(expr_ref(n->get_expr(), m));
      }
      else if (r && !j.is_marked()) {
        sm.close(expr_ref(n->get_expr(), m));
        r = nullptr;
      }

      SASSERT(n->m_target);
      n = n->m_target;
    }
    open_prem.append(sm.m_prem);
    return r;
  }

  // Purification pre-pass (cf. MiniSat's fixrec / RUP-chain purify_reason):
  // walk the branch and re-mark maximal runs of unmarked edges that lie
  // strictly between marked edges when the summarized side alone entails the
  // equality of the run's endpoints. The two enclosing marked runs then fuse
  // into one, and the summary loses their two facing boundary equalities.
  // Requiring marked edges on both flanks keeps run endpoints on terms that
  // occur in summarized-side reasoning, so the summary's vocabulary is
  // unchanged. Congruence edges inside a purified run are absorbed like any
  // other marked edge: the run is summarized by its endpoints, so their
  // internal structure is not needed.
  void euf_summarizer::purify_branch(enode *n, enode *lca) {
    if (!m_entails || n == lca)
      return;
    ptr_vector<enode> path;
    for (enode *p = n; p != lca; p = p->m_target)
      path.push_back(p);
    path.push_back(lca);
    unsigned k = path.size() - 1; // number of edges; edge i = (path[i], path[i+1])
    unsigned i = 0;
    while (i < k) {
      if (path[i]->m_justification.is_marked()) {
        ++i;
        continue;
      }
      unsigned j = i;
      while (j < k && !path[j]->m_justification.is_marked())
        ++j;
      // maximal unmarked segment [i, j); flanked by marked edges iff i > 0 and j < k
      if (i > 0 && j < k && m_entails(path[i]->get_expr(), path[j]->get_expr())) {
        for (unsigned l = i; l < j; ++l)
          path[l]->m_justification.set_mark(true);
        ++m_purified;
      }
      i = j;
    }
  }

  void euf_summarizer::summarize_trans(enode *a, enode *b, expr_ref &a_sum, expr_ref &b_sum,
                                       expr_ref_vector &a_prem, expr_ref_vector &b_prem) {
    enode *lca = m_eg.find_lca(a, b);
    purify_branch(a, lca);
    purify_branch(b, lca);
    expr_ref_vector lprem(m), rprem(m);
    expr_ref lhs(m);
    lhs = summarize_branch(a, lca, a_sum, a_prem, lprem);
    expr_ref rhs(m);
    rhs = summarize_branch(b, lca, b_sum, b_prem, rprem);
    if (!lhs)
      lhs = lca->get_expr();
    if (!rhs)
      rhs = lca->get_expr();

    // The run spanning the lca is the union of both branches' open runs.
    expr_ref_vector span(m);
    span.append(lprem);
    for (expr *p : rprem)
      push_unique(span, p);

    if (lhs == a->get_expr() && a_sum == nullptr) {
      a_sum = rhs;
      a_prem.reset();
      a_prem.append(span);
    }
    if (rhs == b->get_expr() && b_sum == nullptr) {
      b_sum = lhs;
      b_prem.reset();
      b_prem.append(span);
    }

    if (lhs != a->get_expr() && rhs != b->get_expr())
      emit(span, lhs, rhs);
  }

  const euf_summarizer::congr_sum &euf_summarizer::summarize_congr(enode *c) {

    SASSERT(c->m_justification.is_congruence());

    justification &j = c->m_justification;
    if (m_ccsum.count(&j) > 0)
      return m_ccsum.find(&j)->second;

    m_ccsum.emplace(&j, m); // create new entry in the cache
    congr_sum &csum = m_ccsum.find(&j)->second;

    expr *L = c->get_expr();
    expr *R = c->m_target->get_expr();

    // A "flat" endpoint is one the summarized side cannot use (it contains a
    // symbol local to the other side), so no summarized run can reach it: the
    // arguments' summarized-side runs on that side are emitted standalone and
    // the endpoint itself serves as the boundary. Legacy mode (no shared-symbol
    // oracle) decides by the function symbol alone, as the code originally did.
    bool flatL, flatR;
    if (legacy_modes())
      flatL = flatR = !sym_colorable(c);
    else {
      flatL = !term_usable(L);
      flatR = !term_usable(R);
    }
    bool both_flat = flatL && flatR;

    expr_ref a_sum(m), b_sum(m);
    expr_ref_vector a_prem(m), b_prem(m);
    expr_ref_vector horn_prem(m);   // HORN: boundary equalities + their premises
    expr_ref_vector nested(m);      // premises of fully summarized-side argument paths
    unsigned init_sz = m_sum.size();
    unsigned last_sz = init_sz;

    auto ach = enode_args(c);
    auto bch = enode_args(c->m_target);
    for (auto a_it = ach.begin(), b_it = bch.begin(); a_it != ach.end();
         ++a_it, ++b_it) {
      enode *an = *a_it;
      enode *bn = *b_it;

      a_sum = nullptr;
      b_sum = nullptr;
      a_prem.reset();
      b_prem.reset();

      bool fully_a = false;

      if (an == bn) {
        // Identical argument: trivially summarized-side. (Legacy mode kept the
        // original miscount, treating it as not colorable.)
        fully_a = !legacy_modes();
      }
      else {
        summarize_trans(an, bn, a_sum, b_sum, a_prem, b_prem);
        fully_a = m_sum.size() == last_sz && a_sum == bn->get_expr() && b_sum == an->get_expr();
      }

      if (both_flat) {
        // Neither endpoint is usable: the arguments' summarized runs are the
        // whole contribution, each emitted at its shared boundary (as sum_eq does).
        if (an != bn) {
          if (a_sum && a_sum != an->get_expr())
            emit(a_prem, an->get_expr(), a_sum);
          if (b_sum && b_sum != bn->get_expr() && a_sum != bn->get_expr())
            emit(b_prem, bn->get_expr(), b_sum);
          // Fully-colorable argument: its summary is the bare argument equality.
          if (m_sum.size() == last_sz && fully_a)
            emit(a_prem, an->get_expr(), bn->get_expr());
        }
        expr_ref arg1(a_sum ? a_sum : an->get_expr(), m);
        expr_ref arg2(b_sum ? b_sum : bn->get_expr(), m);
        csum.insert_args(arg1, arg2, false);
        last_sz = m_sum.size();
        continue;
      }

      if (fully_a && an != bn) {
        // an = bn is proved entirely by the summarized side (under the nested
        // premises a_prem == b_prem); represent the position by an on both sides.
        a_sum = b_sum;
      }
      // A flat side's boundary is the endpoint itself: its argument runs cannot
      // join a run through the endpoint, so they are emitted standalone.
      if (flatL) {
        if (a_sum && a_sum != an->get_expr())
          emit(a_prem, an->get_expr(), a_sum);
        a_sum = nullptr;
      }
      if (flatR) {
        if (b_sum && b_sum != bn->get_expr() && (flatL || a_sum != bn->get_expr()))
          emit(b_prem, bn->get_expr(), b_sum);
        b_sum = nullptr;
      }

      expr_ref arg1(a_sum ? a_sum : an->get_expr(), m);
      expr_ref arg2(b_sum ? b_sum : bn->get_expr(), m);
      csum.insert_args(arg1, arg2, fully_a);

      if (fully_a) {
        // The equality an = bn used on the right side rests on the nested premises.
        for (expr *p : a_prem)
          push_unique(nested, p);
      }
      else {
        // HORN: the boundary equality arg1 = arg2, under the premises of the
        // two boundary runs, justifies the congruence for the run passing through.
        if (arg1 != arg2)
          push_unique(horn_prem, mk_eq_ordered(m, arg1, arg2));
        for (expr *p : a_prem) push_unique(horn_prem, p);
        for (expr *p : b_prem) push_unique(horn_prem, p);
        // BOUNDARY: each boundary application rests on its own side's run premises.
        for (expr *p : a_prem) push_unique(csum.left_prem(), p);
        for (expr *p : b_prem) push_unique(csum.right_prem(), p);
      }
      last_sz = m_sum.size();
    }

    if (both_flat) {
      csum.set_mode(congr_sum::ARG_EQS);
      return csum;
    }

    // Fold the congruence into the run only if all arguments are summarized-side
    // and both endpoints are usable by that side.
    if (!flatL && !flatR && csum.is_colorable()) {
      csum.reset();
      c->m_justification.set_mark(true);
      m_sum.shrink(init_sz);
      csum.set_mode(congr_sum::MARKED);
      csum.prem().append(nested);
      return csum;
    }

    // Cut the run at the boundary applications when they are shared terms;
    // otherwise let the run pass through and carry the argument equalities as
    // premises. A flat side's application is the endpoint itself, which the run
    // never enters, so BOUNDARY is the only option there.
    bool boundary = legacy_modes() || flatL || flatR;
    if (!boundary) {
      expr_ref bl = rewrite_args(L, csum.left_args());
      expr_ref br = rewrite_args(R, csum.right_args());
      boundary = term_shared(bl) && term_shared(br);
    }
    if (boundary) {
      csum.set_mode(congr_sum::BOUNDARY);
      for (expr *p : nested)
        push_unique(csum.right_prem(), p);
    }
    else {
      csum.set_mode(congr_sum::HORN);
      csum.prem().append(horn_prem);
      for (expr *p : nested)
        push_unique(csum.prem(), p);
    }
    return csum;
  }

  void euf_summarizer::sum_eq(enode *a, enode *b) {
    SASSERT(a->get_root() == b->get_root());

    expr_ref a_sum(m), b_sum(m);
    expr_ref_vector a_prem(m), b_prem(m);
    summarize_trans(a, b, a_sum, b_sum, a_prem, b_prem);
    if (a_sum && a_sum != a->get_expr())
      emit(a_prem, a->get_expr(), a_sum);
    if (b_sum && b_sum != b->get_expr() && a_sum != b->get_expr())
      emit(b_prem, b->get_expr(), b_sum);
  }

} // namespace euf
