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

  expr_ref euf_summarizer::summarize_branch(enode *n, enode *lca, expr_ref &first_sum) {

    expr_ref r(nullptr, m); // beginning of summary

    if (n == lca)
      return r;

    const congr_sum *csum = nullptr;
    sum_manager sm(m_sum, n->get_expr(), first_sum);

    while (n != lca) {
      justification &j = n->m_justification;
      if (j.is_congruence() && !j.is_marked()) {
        csum = &summarize_congr(n); // marks j if colorable
        // Only emit a congruence boundary (a function application over the
        // summarized arguments) when the function symbol is usable in the
        // summarized side. Otherwise the argument equalities, already pushed to
        // m_sum by summarize_congr, are the boundary.
        if (!j.is_marked() && sym_colorable(n)) {
          // summary is not colorable
          if (r) { // summary started, close
            sm.close(rewrite_args(n->get_expr(), csum->left_args()));
          } else { // open and close
            sm.open(expr_ref(n->get_expr(), m));
            sm.close(rewrite_args(n->get_expr(), csum->left_args()));
          }
          // open for the next one
          r = sm.open(rewrite_args(n->m_target->get_expr(), csum->right_args()));
        }
      }
      if (!r && j.is_marked()) { // new summary starts (colorable)
        r = sm.open(expr_ref(n->get_expr(), m));
      } else if (r && !j.is_marked() && !j.is_congruence()) {
        sm.close(expr_ref(n->get_expr(), m));
        r = nullptr;
      }

      SASSERT(n->m_target);
      n = n->m_target;
    }
    return r;
  }

  void euf_summarizer::summarize_trans(enode *a, enode *b, expr_ref &a_sum,
                                       expr_ref &b_sum) {
    enode *lca = m_eg.find_lca(a, b);
    expr_ref lhs(m);
    lhs = summarize_branch(a, lca, a_sum);
    expr_ref rhs(m);
    rhs = summarize_branch(b, lca, b_sum);
    if (!lhs)
      lhs = lca->get_expr();
    if (!rhs)
      rhs = lca->get_expr();

    if (lhs == a->get_expr() && a_sum == nullptr)
      a_sum = rhs;
    if (rhs == b->get_expr() && b_sum == nullptr)
      b_sum = lhs;

    if (lhs != a->get_expr() && rhs != b->get_expr() && lhs != rhs)
      m_sum.push_back(mk_eq_ordered(m, lhs, rhs));
  }

  const euf_summarizer::congr_sum &euf_summarizer::summarize_congr(enode *c) {

    SASSERT(c->m_justification.is_congruence());

    justification &j = c->m_justification;
    if (m_ccsum.count(&j) > 0)
      return m_ccsum.find(&j)->second;

    m_ccsum.emplace(&j, m); // create new entry in the cache
    congr_sum &csum = m_ccsum.find(&j)->second;

    // When the function symbol is not usable in the summarized side (local to
    // the other side), the congruence F(..)=F(..) cannot appear in the summary;
    // its contribution is the equalities between the (summarized) arguments.
    bool f_colorable = sym_colorable(c);

    expr_ref a_sum(m), b_sum(m);
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

      bool arg_is_B = false;

      if (an != bn) {
        summarize_trans(an, bn, a_sum, b_sum);
        if (!f_colorable) {
          // Emit the argument equality at its shared boundary (as sum_eq does).
          if (a_sum && a_sum != an->get_expr())
            m_sum.push_back(mk_eq_ordered(m, an->get_expr(), a_sum));
          if (b_sum && b_sum != bn->get_expr() && a_sum != bn->get_expr())
            m_sum.push_back(mk_eq_ordered(m, bn->get_expr(), b_sum));
          // Fully-colorable argument: its summary is the bare argument equality.
          if (m_sum.size() == last_sz && a_sum == bn->get_expr() && b_sum == an->get_expr())
            m_sum.push_back(mk_eq_ordered(m, an->get_expr(), bn->get_expr()));
          last_sz = m_sum.size();
        }
        else {
          if (m_sum.size() == last_sz) {
            if (a_sum == bn->get_expr() && b_sum == an->get_expr()) {
              a_sum = b_sum;
              arg_is_B = true;
            }
          }
          last_sz = m_sum.size();
        }
      }

      expr_ref arg1(m);
      expr_ref arg2(m);
      arg1 = a_sum ? a_sum : an->get_expr();
      arg2 = b_sum ? b_sum : bn->get_expr();
      csum.insert_args(arg1, arg2, arg_is_B);
    }

    // Fold the congruence into the summary only if all arguments are colorable
    // AND the function symbol itself is usable in the summarized side.
    if (f_colorable && csum.is_colorable()) {
      csum.reset();
      c->m_justification.set_mark(true);
      m_sum.shrink(init_sz);
    }
    return csum;
  }

  void euf_summarizer::sum_eq(enode *a, enode *b) {
    SASSERT(a->get_root() == b->get_root());

    expr_ref a_sum(m), b_sum(m);
    summarize_trans(a, b, a_sum, b_sum);
    if (a_sum && a_sum != a->get_expr())
      m_sum.push_back(mk_eq_ordered(m, a->get_expr(), a_sum));
    if (b_sum && b_sum != b->get_expr() && a_sum != b->get_expr())
      m_sum.push_back(mk_eq_ordered(m, b->get_expr(), b_sum));
  }

} // namespace euf
