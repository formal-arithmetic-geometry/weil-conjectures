## What changed

Proved `AlgebraicGeometry.Scheme.powerSeries_mem_variables_pow_of_punctured_germs`
with its signature unchanged. Added two proved helper modules:
`PowerSeriesLocalKernelCoefficients` and `DepthTwoPuncturedFunctionDetection`.
The proof first kills each low-degree coefficient locally, then globally by
associated-prime detection, and applies the existing proved coefficient criterion.
All proof dependencies are ordinary imports; existing public imports are unchanged.
The unit route is unchanged: this is a coefficientwise proof of the fixed-order
calculation inside its power-series full-faithfulness input.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.powerSeries_mem_variables_pow_of_punctured_germs`
(node `lem-sbc-power-series-punctured-ideal-detection`). Added 0 holes; split off 0.

Both new public theorems are fully proved:
- `AlgebraicGeometry.Scheme.powerSeries_low_coeff_germ_eq_zero_of_kernel_pow`
  (`lem-sbc-power-series-local-kernel-coefficients`).
- `AlgebraicGeometry.Scheme.eq_zero_of_depth_two_punctured_germs`
  (`lem-sbc-depth-two-punctured-function-detection`).

No `sorry` remains in any delivered module. Single-file compilation and the
required delivery axiom probes verify the proofs. The local coefficient theorem
also covers d=0 and n=0 and requires no depth or Noetherianity; the main theorem's
hypotheses and conclusion have not changed. No definition is introduced.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction`.
The node `lem-sbc-depth-two-hartogs-restriction` is no longer a dependency of this
item. Its isomorphism and finite-free thickening comparison are stronger than
needed for detection: positive-depth exclusion of the maximal associated prime
suffices. No claim is made that this module is globally unreachable; other
items may still use it.

The original localization nodes
`lem-weil-pbc-spec-map-stalk-localization` and
`lem-weil-pbc-affine-open-stalk-localization` remain needed through the local
coefficient helper; their Mathlib APIs are used. No other original dependency
is pruned. No public import was removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface problem was found. The planned full Hartogs
quotient-section comparison is unnecessary for this injectivity-only assertion.
We instead localize coefficients and use associated-prime detection. Sources:
[Stacks 0EY9](https://stacks.math.columbia.edu/tag/0EY9),
[Stacks 0311](https://stacks.math.columbia.edu/tag/0311), and
[Stacks 00LL](https://stacks.math.columbia.edu/tag/00LL).
The private depth-zero helper follows the already proved argument in
`DepthOneRestrictionInjective`, with no adaptation of that module.

## New nodes

`lem-sbc-power-series-local-kernel-coefficients` records the proved local
calculation, in `PowerSeriesLocalKernelCoefficients`. Its private algebra helper
extends coefficientwise localization to B_q and sends kernel powers into
variables-ideal powers over A_p; canonical stalk isomorphisms finish the proof.

`lem-sbc-depth-two-punctured-function-detection` records the proved global
coefficient detection, in `DepthTwoPuncturedFunctionDetection`. Positive depth
excludes the maximal associated prime and the existing proved localization
injection detects zero. No change records or forced adaptations are needed.

## Second reading by T4

1. **Interface unchanged — PASS.** Compared the item with the repository using
   `diff` and compared the existing theorem header byte for byte. Its hypotheses,
   conclusion, public visibility, and existing public imports are unchanged. No
   definition or target was altered. The two added declarations have their own
   modules and nodes; neither is an adaptation of another held module.
2. **Kernel-checked proof — PASS.** Compiled all three modules through `lcompile.py`.
   Scanned all delivered Lean for `sorry`, axioms, unsafe/opaque declarations,
   implementation substitutions and externs: none. A scratch module printed axioms
   of the item and both public helpers: exactly `propext`, `Classical.choice`,
   `Quot.sound`, with no `sorryAx`. No data is selected from an unproved theorem.
3. **Intermediate statements — PASS.** No holed statement was split off. Read both
   proved helper statements and their complete docstring arguments. The local
   calculation works for any commutative ring and open, including d=0 and n=0;
   at n=0 its coefficient condition is empty. The global detection uses actual
   stalk zeros, so nilpotents cause no problem; positive depth excludes the
   maximal associated prime. The helpers are strictly different parts of the
   argument, not copies of the item's hypotheses and conclusion. Independent
   searches used leanfinder on vanishing at nonmaximal prime localizations,
   loogle on coefficient/ideal APIs, and grep on constant-coefficient kernels
   and associated-prime depth; no shorter exact theorem was found. The loogle
   query's `Ideal.pow` identifier was rejected, so it supplies no negative
   evidence. Searched the library with low-coefficient/kernel and depth phrases
   and read `DepthOneRestrictionInjective`, the associated-prime injection, and
   the combined-ideal coefficient criterion. The reused private depth argument
   is inaccessible from the earlier module; using its general sheaf theorem
   would add substantially more machinery.
4. **Route and pruning — PASS.** Followed the item downward through localization
   of coefficients, associated-prime detection, and the proved coefficient
   criterion. The stronger Hartogs restriction result is unnecessary and is
   listed above. The two original stalk-localization nodes remain used through
   the local helper. Read `dag/units/sk-prop-input-spreading.json`: the fixed-order
   calculation remains inside the unit's 0EY9 full-faithfulness input; no unit
   statement or step is bypassed. Its existing empty `realized` arrays are
   unchanged. Existing public imports remain; new helpers expose only imports
   needed for signatures, with proof-specific imports ordinary.
5. **DAG agrees — PASS.** Read all three delivered nodes and the referenced
   declarations. The item's three proof steps correspond exactly to its Lean
   proof; each helper's steps and proof dependencies describe its proof. New
   nodes have source, statement dependencies, proof origin, search records,
   creation/blueprint metadata and verbatim public signatures. No new holes
   are concealed in these records.

Changed the extra space before the item's proof to restore its original header
exactly; updated its proof docstring from the abandoned Hartogs argument to the
actual coefficient argument; replaced `Mathlib.AlgebraicGeometry.Noetherian` by
`Mathlib.AlgebraicGeometry.AffineScheme` in both new helper modules. Recompiled
and reran the three axiom probes after these repairs. Closed 1 original hole,
added 0 holes; this is a proof, not a decomposition.
