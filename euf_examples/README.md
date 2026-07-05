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

The pre-existing `iuc_cubes-*.smt2` and `complex_itp.smt2` in the
repository root exercise the same pipeline on congruence-heavy cubes.
