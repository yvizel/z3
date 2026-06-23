/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    proof_mark.h

Abstract:

    A/B markings for proof clauses, variables and trail literals.

    The markings implement the A/B partition used for Craig interpolation
    (cf. Gurfinkel, Vizel, FMCAD 2014). A mark is a small bit-set over the
    labels {A, B}:

      - Original (assumed) clauses are marked A or B, but never both.
      - An inferred clause is marked with the union (bitwise OR) of the
        marks of the clauses it was derived from: only-A premises -> A,
        only-B premises -> B, mixed premises -> AB.
      - A variable is marked with the union of the marks of the original
        clauses it occurs in.

    Because the inference rule is exactly set-union, the mark is represented
    as a 2-bit value and combined with bitwise OR.

Author:

    Yakir Vizel 2025

--*/
#pragma once

namespace sat {

    enum ab_mark : unsigned char {
        MARK_NONE = 0,   // no marking supplied (interpolation disabled)
        MARK_A    = 1,   // bit 0
        MARK_B    = 2,   // bit 1
        MARK_AB   = 3    // both A and B
    };

    inline ab_mark operator|(ab_mark a, ab_mark b) {
        return static_cast<ab_mark>(static_cast<unsigned char>(a) | static_cast<unsigned char>(b));
    }

    inline ab_mark& operator|=(ab_mark& a, ab_mark b) {
        a = a | b;
        return a;
    }

    inline bool is_marked_a(ab_mark m) { return (m & MARK_A) != 0; }
    inline bool is_marked_b(ab_mark m) { return (m & MARK_B) != 0; }

    inline char const* ab_mark_to_string(ab_mark m) {
        switch (m) {
        case MARK_A:  return "A";
        case MARK_B:  return "B";
        case MARK_AB: return "AB";
        default:      return "none";
        }
    }

}
