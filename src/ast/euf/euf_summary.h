/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_summary.h

Abstract:

    Summaries for EUF interpolants (IUCs).

    Given an egraph whose merge justifications are partially marked (the marked
    edges belong to the part to be summarized for an A/B interpolation problem),
    euf_summarizer walks the proof forest between two equal nodes and produces a
    conjunction of equalities over shared terms that captures the marked
    reasoning, introducing shared function applications at congruence boundaries.

Author:

    Isabel Garcia Contreras

--*/

#pragma once

#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_justification.h"
#include <functional>
#include <unordered_map>

namespace euf {

// Build an equality with a canonical argument order (by ast id) so that
// symmetric equalities (a=b and b=a) share the same expression and fold away.
inline expr* mk_eq_ordered(ast_manager& m, expr* a, expr* b) {
    return a->get_id() <= b->get_id() ? m.mk_eq(a, b) : m.mk_eq(b, a);
}

class euf_summarizer {

  class congr_sum {
    expr_ref_vector m_left_args;
    expr_ref_vector m_right_args;
    std::vector<bool> m_colorable;

  public:
    congr_sum(ast_manager &m) : m_left_args(m), m_right_args(m){};

    void insert_args(expr_ref l_arg, expr_ref r_arg, bool colorable) {
      m_left_args.push_back(l_arg);
      m_right_args.push_back(r_arg);
      m_colorable.push_back(colorable);
    }

    bool is_colorable() const {
      for (unsigned i = 0; i < m_colorable.size(); i++)
        if (!m_colorable[i]) return false;
      return true;
    }
    void reset() {
      m_left_args.reset();
      m_right_args.reset();
    }

    const expr_ref_vector& left_args() const { return m_left_args; }
    const expr_ref_vector& right_args() const { return m_right_args; }
  };

  struct sum_manager {
    ast_manager &m;
    expr_ref_vector &m_sum;
    expr_ref m_begin;
    expr * m_first_expr;
    expr_ref &m_first_sum;
    bool begins_colorable = false;

    sum_manager(expr_ref_vector &sum, expr * first_expr, expr_ref &first_sum)
        : m(sum.get_manager()), m_sum(sum), m_begin(sum.get_manager()),
          m_first_expr(first_expr), m_first_sum(first_sum) {
      m_begin = nullptr;
    }

    expr_ref open(expr_ref begin) {
      SASSERT(begin);
      if (begin == m_first_expr) // do not push in the summary, store in m_first_sum when closing
        begins_colorable = true;
      else
        m_begin = begin;
      return begin;
    }
    void close(expr_ref end) {
      SASSERT(end);
      if (begins_colorable) {
        m_first_sum = end;
        begins_colorable = false;
      } else {
        if (m_begin != end)
          m_sum.push_back(mk_eq_ordered(m, m_begin, end));
      }
    }
  };

  // cache for congruences that have been summarized
  std::unordered_map<justification *, congr_sum> m_ccsum;
  egraph &m_eg;
  expr_ref_vector &m_sum;
  ast_manager &m;
  // True if a function symbol is usable in the side being summarized (it is
  // shared or local to that side). When false, a congruence over it cannot be
  // expressed in the summary, so only its argument equalities are kept.
  std::function<bool(func_decl*)> m_sym_colorable;

  bool sym_colorable(enode* n) const {
    return !m_sym_colorable || !n->get_decl() || m_sym_colorable(n->get_decl());
  }

  void summarize_trans(enode *a, enode *b, expr_ref &a_sum, expr_ref &b_sum);
  const congr_sum &summarize_congr(enode *c);
  expr_ref summarize_branch(enode *n, enode *lca, expr_ref &first_sum);

public:
  euf_summarizer(egraph &eg, expr_ref_vector &sum,
                 std::function<bool(func_decl*)> sym_colorable = nullptr)
      : m_eg(eg), m_sum(sum), m(eg.get_manager()), m_sym_colorable(std::move(sym_colorable)){};
  void sum_eq(enode *a, enode *b);
};

} // namespace euf
