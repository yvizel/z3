/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_summary.h

Abstract:

    Summaries for EUF interpolants (IUCs).

    Given an egraph whose merge justifications are partially marked (the marked
    edges belong to the part to be summarized for an A/B interpolation problem),
    euf_summarizer walks the proof forest between two equal nodes and produces a
    conjunction of Horn clauses over shared terms that captures the marked
    reasoning. Each maximal run of summarized-side edges contributes one clause
    (premises -> begin = end); the premises are the boundary equalities of the
    other-side argument paths that justify congruence edges the run passes
    through (cf. Fuchs, Goel, Grundy, Krstic, Tinelli, "Ground interpolation
    for the theory of equality", TACAS 2009). Plain equalities are the special
    case of an empty premise set.

    A congruence edge L = F(a..) -- F(b..) = R is summarized in one of four
    modes, decided by the color of its endpoint terms (not of F alone):

      - MARKED:   every argument path is summarized-side; the edge joins the run.
      - BOUNDARY: the run is cut at the edge and continues from a rewritten
                  application F(a'..) / F(b'..) over the arguments' boundary
                  terms - only when those applications are shared terms.
      - HORN:     the run passes through the edge; the arguments' boundary
                  equalities a' = b' become premises of the run's clause.
      - ARG_EQS:  neither endpoint is usable by the summarized side; only the
                  arguments' summarized-side runs are emitted, standalone.

Author:

    Isabel Garcia Contreras

--*/

#pragma once

#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_justification.h"
#include "util/obj_hashtable.h"
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
  public:
    enum mode_t { ARG_EQS, BOUNDARY, HORN, MARKED };

  private:
    expr_ref_vector m_left_args;
    expr_ref_vector m_right_args;
    std::vector<bool> m_colorable;
    // BOUNDARY: premises of the argument runs feeding the left / right
    // boundary application. HORN and MARKED: premises the enclosing run
    // acquires by passing through the edge.
    expr_ref_vector m_left_prem;
    expr_ref_vector m_right_prem;
    expr_ref_vector m_prem;
    mode_t m_mode = ARG_EQS;

  public:
    congr_sum(ast_manager &m)
        : m_left_args(m), m_right_args(m), m_left_prem(m), m_right_prem(m), m_prem(m) {}

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

    mode_t mode() const { return m_mode; }
    void set_mode(mode_t md) { m_mode = md; }

    const expr_ref_vector& left_args() const { return m_left_args; }
    const expr_ref_vector& right_args() const { return m_right_args; }
    expr_ref_vector& left_prem() { return m_left_prem; }
    expr_ref_vector& right_prem() { return m_right_prem; }
    expr_ref_vector& prem() { return m_prem; }
    const expr_ref_vector& left_prem() const { return m_left_prem; }
    const expr_ref_vector& right_prem() const { return m_right_prem; }
    const expr_ref_vector& prem() const { return m_prem; }
  };

  // Tracks the run currently being summarized along one branch: where it
  // began, and the premises it has picked up so far. The run that begins at
  // the branch's first node is not emitted but handed back to the caller via
  // (m_first_sum, m_first_prem), so the caller can decide how to close it.
  struct sum_manager {
    euf_summarizer &s;
    ast_manager &m;
    expr_ref m_begin;
    expr * m_first_expr;
    expr_ref &m_first_sum;
    expr_ref_vector &m_first_prem;
    expr_ref_vector m_prem;        // premises of the open run
    bool begins_colorable = false;

    sum_manager(euf_summarizer &s, expr * first_expr, expr_ref &first_sum, expr_ref_vector &first_prem)
        : s(s), m(s.m), m_begin(s.m), m_first_expr(first_expr),
          m_first_sum(first_sum), m_first_prem(first_prem), m_prem(s.m) {
      m_begin = nullptr;
    }

    expr_ref open(expr_ref begin) {
      SASSERT(begin);
      if (begin == m_first_expr) // do not push in the summary, store in m_first_sum when closing
        begins_colorable = true;
      else
        m_begin = begin;
      m_prem.reset();
      return begin;
    }
    void add_premises(expr_ref_vector const &prem) {
      for (expr *p : prem)
        push_unique(m_prem, p);
    }
    void close(expr_ref end) {
      SASSERT(end);
      if (begins_colorable) {
        m_first_sum = end;
        m_first_prem.reset();
        m_first_prem.append(m_prem);
        begins_colorable = false;
      } else {
        s.emit(m_prem, m_begin, end);
      }
      m_prem.reset();
    }
  };

  // cache for congruences that have been summarized
  std::unordered_map<justification *, congr_sum> m_ccsum;
  egraph &m_eg;
  expr_ref_vector &m_sum;
  ast_manager &m;
  // True if a function symbol is usable in the side being summarized (it is
  // shared or local to that side). A congruence over a symbol that is not
  // usable cannot join a summarized run.
  std::function<bool(func_decl*)> m_sym_colorable;
  // True if a function symbol is shared by both sides, i.e. may occur in the
  // summary. When unset, "shared" defaults to "usable" and the summarizer
  // behaves as it did before Horn summaries existed (boundary applications
  // are emitted for every usable symbol, never a Horn clause).
  std::function<bool(func_decl*)> m_sym_shared;
  // Optional purification oracle (FMCAD'14-style proof reordering for EUF):
  // entails(x, y) holds when the summarized side alone already entails
  // x = y. When set, walked paths are purified first: a run of other-side
  // edges lying strictly between summarized-side edges whose endpoints the
  // oracle equates is re-marked as summarized-side, fusing the enclosing
  // marked runs into one and dropping their facing boundary equalities from
  // the summary. Boundaries never move to new terms, so the summary's
  // vocabulary is unaffected.
  std::function<bool(expr*, expr*)> m_entails;
  unsigned m_purified = 0;
  // term -> bit 0: usable by the summarized side, bit 1: shared
  obj_map<expr, unsigned> m_term_color;

  bool sym_colorable(func_decl* f) const { return !m_sym_colorable || m_sym_colorable(f); }
  bool sym_shared(func_decl* f) const { return m_sym_shared ? m_sym_shared(f) : sym_colorable(f); }
  bool sym_colorable(enode* n) const { return !n->get_decl() || sym_colorable(n->get_decl()); }
  bool legacy_modes() const { return !m_sym_shared; }
  unsigned term_color(expr* e);
  bool term_usable(expr* e) { return (term_color(e) & 1) != 0; }
  bool term_shared(expr* e) { return (term_color(e) & 2) != 0; }

  static void push_unique(expr_ref_vector& v, expr* e) {
    if (!v.contains(e))
      v.push_back(e);
  }
  // Push (prem -> lhs = rhs) to the summary; a plain equality when prem is
  // empty, nothing when lhs == rhs or the conclusion is among the premises.
  void emit(expr_ref_vector const& prem, expr* lhs, expr* rhs);

  void purify_branch(enode *n, enode *lca);
  void summarize_trans(enode *a, enode *b, expr_ref &a_sum, expr_ref &b_sum,
                       expr_ref_vector &a_prem, expr_ref_vector &b_prem);
  const congr_sum &summarize_congr(enode *c);
  expr_ref summarize_branch(enode *n, enode *lca, expr_ref &first_sum,
                            expr_ref_vector &first_prem, expr_ref_vector &open_prem);

public:
  euf_summarizer(egraph &eg, expr_ref_vector &sum,
                 std::function<bool(func_decl*)> sym_colorable = nullptr,
                 std::function<bool(func_decl*)> sym_shared = nullptr)
      : m_eg(eg), m_sum(sum), m(eg.get_manager()),
        m_sym_colorable(std::move(sym_colorable)), m_sym_shared(std::move(sym_shared)){};
  void set_side_entails(std::function<bool(expr*, expr*)> entails) { m_entails = std::move(entails); }
  unsigned num_purified() const { return m_purified; }
  void sum_eq(enode *a, enode *b);
};

} // namespace euf
