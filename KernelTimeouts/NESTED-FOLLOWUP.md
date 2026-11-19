# Nested-data follow-up run record

This record closes the measurement pass requested by the lead note. The
timed controls below were run from the current branch with Lean/Mathlib
4.35.0, one Lean thread, ordinary kernel checking, and `/usr/bin/time -v`.

| Case | Probe | Result | Wall s | CPU user+sys s | Peak RSS KB |
|---|---|---|---:|---:|---:|
| OrderedSpectralRawLattices | `probes/nd/After.lean` | checked | 10.08 | 13.71+0.95 | 2,571,072 |
| FiniteBaseChangeRestrictionMateTransport | `probes/nd/TransportHB.lean` | checked | 4.38 | 4.31+0.90 | 2,337,048 |
| EtaleHomComparisonReversedExact | `probes/nd/TransportHV.lean` | checked | 3.37 | 2.46+1.06 | 3,204,732 |
| F66Adj | `probes/nd/ReplaceHR.lean` | checked | 3.49 | 2.82+1.00 | 2,857,796 |
| ImageHomCounit | `probes/nd/UniformInferred.lean` | checked | 2.59 | 1.73+0.94 | 2,815,584 |
| IntegralComparisonPullbackRealizationShifts | `probes/nd/AlignInstance.lean` | exact-site diagnostic; later `sorry` | 84.14 | 85.35+1.35 | 8,539,300 |
| RealPurity | `probes/nd/AlignBothRing.lean` | kernel deterministic timeout | 58.79 | 58.79+1.26 | 5,616,320 |

The first five rows are matched fast controls retaining the original
consumer. The last two rows are exact-site probes, not successful theorem
proofs: IntegralComparison keeps the original `change` site and then
discards later work, while RealPurity times out at `exact h`.

## Replay and curve validity

The A probes retain the original consumer and expose the changed
representation at the recorded cost site. They do not all meet the strict
section-2.2 requirement of replaying a previously elaborated term with every
instance argument explicit. The generic Etale helper already uses an `@`
application with explicit type and category slots, and the finite-base
helper receives its comparison data explicitly; the remaining category,
ring, derived-category, and wrapper arguments are still inferred by the
source. These are reported as partial replays, not promoted to strict
Level-1 evidence.

The assigned B harnesses (OrderedSpectralRawLattices,
FiniteBaseChangeRestrictionMateTransport, EtaleHomComparisonReversedExact,
and F66Adj) and the assigned C harness (OrderedSpectralRawLattices) were
validated against the exact source contexts. Adding an artificial class
chain or repeated field without rebuilding the imported declaration leaves
the stored instance arguments unchanged; rebuilding the whole declaration
changes the consumer and loses the measured site. No valid depth or fanout
curve therefore exists in this revision. This is a validity result, not a
zero-cost measurement, and the per-case records keep the attempted factor
separate from the exact-site timings.

No source-level priority change is treated as rewriting an imported term.
No skipped-kernel, `sorry`, or axiom result is counted as a checked control.
