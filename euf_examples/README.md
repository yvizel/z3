# EUF interpolation examples

Test instances for EUF Craig interpolation via proof trimming and replay
(FMCAD'14 "DRUPing for Interpolants" proof reordering + labeled
interpolation systems). Each file is self-contained: solving it logs a
clause proof next to the current directory, which is then replayed with
interpolation enabled.

## Usage

```
z3 <example>.smt2                       # solve; writes <example>_proof.smt2
z3 solver.proof.trim=true solver.proof.interpolate=true \
   solver.proof.check_interpolant=true <example>_proof.smt2
```

Useful additional options:

- `solver.proof.reorder=false` — disable colored BCP and RUP-chain
  restructuring (baseline for comparing proof/interpolant structure).
- `solver.proof.itp_labeling=mcmillan|hkp|dual` — labeling of shared
  variables (strongest / symmetric / weakest interpolant).
- `solver.proof.itp_label_opt=colorable` — promote only the shared
  variables occurring in theory lemmas to label ab, so lemma-internal
  chains stay single-colored without paying ab guards on purely
  propositional shared pivots.
- `solver.proof.check_labeling_order=true` — verify
  mcmillan => hkp => dual on the same proof.
- `solver.proof.core_first_bcp=true` — prefer core-marked clauses during
  replay propagation.
- `-v:1` prints the raw (unsimplified) interpolant, `-v:2` additionally
  per-theory-lemma partial interpolants.

## Examples

| file | shape | demonstrates |
|---|---|---|
| `ladder3.smt2` | 3-step alternating A/B equality ladder | small EUF lemmas; replayed correctly even before the trim id/trail fix |
| `ladder4.smt2` | 4-step ladder | minimal proof containing a deletion; historic repro of the trim id/trail misalignment bug |
| `itp_chain.smt2` | 12-step ladder | mid-size mixed-chain EUF lemmas |
| `ladder24.smt2` | 24-step ladder | large proof (~100 steps, ~20 deletions) |
| `wide2/3/4/6/10.smt2` | K parallel 3-step ladders, B refutes the disjunction of their conclusions | deep propositional resolution over many small EUF lemmas; wide10 yields a ~190-step proof |
| `runs15.smt2` | two 15-step implication chains over equality atoms, color pattern A-A-B | proof restructuring factors A-runs into single-colored chains; purely propositional |
| `itp_reorder.smt2` | same shape, 30 steps | flagship reordering demo: with `reorder=true` the raw interpolant is a flat CNF-like conjunction, with `reorder=false` a deeply nested and/or alternation of the same size; also separates the three labelings strictly |
| `theory_ab.smt2` | shared equality (A unit + B clause) driving a congruence | AB-labeled atom inside a theory lemma; exercises the gamma trivial-case path of the labeled T-lemma split |
| `theory_ab2.smt2` | A-local link + shared link feeding a congruence | gamma through the summarizer: under `hkp` the lemma interpolant is a single equality spanning the whole chain, under `mcmillan` it splits at the shared boundary |
| `colorable_opt.smt2` | theory chain + propositional A-A-B chain in one conflict | separates the labelings: `mcmillan` splits the lemma (37 nodes), `hkp` pays ab guards on every chain boundary (47), `mcmillan` + `itp_label_opt=colorable` gets the colorable lemma at 39 |
| `Z3HornGap.smt2` | A-local function links two pairs of shared constants | Horn summaries: the summarizer used to cut the A-run at the boundary applications `F(x)`, `F(y)` and expose the A-local `F`; now the run passes through the congruence and its B-justified argument equality becomes a premise: `(=> (= x y) (= u v))` |
| `horn_local_arg.smt2` | as above, with an A-local argument term `a` between `F(a)` and the shared `x` | the Horn premise is the *boundary* equality `x = y`, not `a = y`; the absorbed A-run `a = x` is never emitted |
| `horn_nested.smt2` | shared `F` over an A-local `G`: `F(G(x)) = F(G(y))` | nested premises: the inner A-local congruence contributes `x = y`, the outer congruence's boundary applications `F(G(x))` are not shared, so the premise propagates up: `(=> (= x y) (= u v))` |
| `horn_mixed_args.smt2` | shared `F` with one A-local-through-`G` position and one B-equal position | boundary applications would embed `G`; Horn mode collects both positions: `(=> (and (= p q) (= x y)) (= u v))` |
| `horn_dual.smt2` | violated disequality in A, B-local `F` | the B-side Horn summary is negated: `(not (=> (= x y) (= u v)))` |
| `boundary_bonly.smt2` | shared `F` applied to a B-local constant on both sides | congruence whose endpoint terms are B-only: only the argument equality `a = b` is emitted (mode ARG_EQS); guards the endpoint-color classification |
| `horn_deep.smt2` | `F(G(H(x))) = F(G(H(y)))`, all three A-local | one premise propagates through three nested HORN congruences: `(=> (= x y) (= u v))` |
| `horn_two_congr.smt2` | `u ~ F(x1)=F(y1) ~ G(x2)=G(y2) ~ v`, F, G A-local | two HORN congruences on one run collect on one clause: `(=> (and (= x2 y2) (= x1 y1)) (= u v))` |
| `horn_two_runs.smt2` | two A-runs through A-local congruences, separated by a B link `p = q` | one Horn clause per run: `(and (=> (= x y) (= p u)) (=> (= x2 y2) (= q v)))` |
| `horn_interleaved.smt2` | argument path `a ~A x ~B y ~A w ~B z ~A d` under A-local `F` | premise is the outer boundary equality `x = z`; the interior A-run is its own conjunct so B can derive the premise: `(and (= y w) (=> (= x z) (= u v)))` |
| `horn_alt_ladder.smt2` | argument ladder `x0 ~A x1 ~B x2 ~A x3 ~B x4` | same pattern as a ladder: `(and (= x2 x3) (=> (= x1 x4) (= u v)))` |
| `horn_ternary.smt2` | ternary A-local `F(x,c,p) = F(y,c,q)` | identical position contributes nothing, the two B-equal positions one premise each: `(=> (and (= x y) (= p q)) (= u v))` |
| `horn_and_boundary.smt2` | `u ~ F(x)=F(y) ~ H(a)=H(b)`, F A-local, H shared | HORN and BOUNDARY on the same run: `(=> (= x y) (= u (H a)))` — the run is cut at the shared `H(a)`. Symbol colors are taken from the original A/B input clauses (not the trimmed core), so `H` counts as shared even if the B clause mentioning it is not needed by the refutation |
| `horn_dual_mixed.smt2` | A-side disequality, B-local `F(G(x),p) = F(G(y),q)` | negated two-premise Horn summary of B: `(not (=> (and (= p q) (= x y)) (= u v)))` |
| `horn_disjunctive.smt2` | A only knows `u = F(x) ∨ u = F(z)`, F A-local | two EUF lemmas with Horn interpolants resolved on an A-local atom; McMillan disjoins them: `(or (=> (= y z) (= u v)) (=> (= x y) (= u v)))` |
| `horn_kitchen_sink.smt2` | A-local F, G, K and shared H in one refutation | nested MARKED-with-premise `G`, two-premise HORN `F`, BOUNDARY `H`, then a second HORN run: `(and (=> (and (= p q) (= x y)) (= u (H a))) (=> (= c d) (= w v)))` |
| `sym_from_input.smt2` | shared `H` whose only B occurrence is in a clause the trimmer drops | symbol colors are taken from the original A/B input clauses, so `H` stays shared and the run is cut at `H(a)`/`H(b)` (BOUNDARY): `(and (=> (= x y) (= u (H a))) (= v (H b)))`; with core-based coloring this degraded to a HORN premise `a = b` |

All `horn_*` / `boundary_bonly` examples produce the same lemma
interpolant under `mcmillan`, `hkp` and `dual` (their conflicts are
single theory lemmas without shared propositional pivots) and pass all
three `check_interpolant` checks.

The pre-existing `iuc_cubes-*.smt2` and `complex_itp.smt2` in the
repository root exercise the same pipeline on congruence-heavy cubes.

## Shape of EUF lemma interpolants

A lemma's partial interpolant is a conjunction of Horn clauses over shared
terms, one per maximal run of summarized-side edges in the colored egraph
proof forest (`src/ast/euf/euf_summary.h`). A congruence edge on the run
is handled by the color of its *endpoint terms*: it joins the run when all
argument paths are summarized-side (MARKED); otherwise the run is cut at
the rewritten applications over the arguments' boundary terms when those
applications are shared (BOUNDARY), or passes through with the boundary
equalities as premises when they are not (HORN); a congruence neither of
whose endpoints is usable by the summarized side only contributes its
arguments' runs (ARG_EQS). Plain equalities are the empty-premise case, so
examples without Horn-mode congruences print exactly as before.
