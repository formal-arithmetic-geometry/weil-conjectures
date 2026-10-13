## What changed

Proved `Algebra.exists_popescu_polynomial_kernel_parameters` without changing its signature,
visibility, or existing docstring. The proof derives regularity from geometric regularity,
uses the flat height formula to identify the source dimension, chooses minimal maximal-ideal
generators, clears denominators, rescales coefficients, and transfers their span to the target
local ring before applying the regular-local generators theorem.

Added `Sheaf.RingTheory.PolynomialCoefficientKernelRescaling`, with the fully proved theorem
`RingTheory.Sequence.exists_polynomial_coefficient_kernel_rescaling`. Its proof identifies the
localized polynomial quotient using Mathlib localization instances, applies Ogoma one index
at a time, and proves that updating the current coefficient preserves every earlier kernel
equality. All six private helpers across the two files are proved.

The new proof imports are private. The existing public imports are unchanged. No statement,
definition, or module held by another group was adapted. The original node and one new node
record the actual proof route.

## Proved and sorry left

Closed the sole original hole:
`Algebra.exists_popescu_polynomial_kernel_parameters`
(`lem-weil-pbc-popescu-polynomial-kernel-parameters`).

Also proved the new declaration
`RingTheory.Sequence.exists_polynomial_coefficient_kernel_rescaling`
(`lem-weil-pbc-polynomial-coefficient-kernel-rescaling`).

Holes closed: 1. Holes added: 0. No `sorry` remains in either delivered module.
This is a proof, not a decomposition into new holes.

Both modules compile together with no errors or warnings through `lcompile.py --all`.
A separate compiled `#print axioms` check confirms that each public theorem depends only on
`propext`, `Classical.choice`, and `Quot.sound`; neither depends on `sorryAx`.
The delivery dry run also compiles both modules and runs the axiom probe and preflight.

## No longer needed

Second reading also removed redundant proof imports
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem` and `Mathlib.RingTheory.Ideal.GoingDown`;
the regular-local-ring dependencies already publicly expose both modules. Removed
the new helper's redundant public import `Mathlib.RingTheory.Noetherian.Basic`; its
other public imports already expose that module.

Removed the direct proof import `Sheaf.RingTheory.RegularRingSmoothAscent`. Polynomial
regularity comes directly from Mathlib's `MvPolynomial.isRegularRing_of_isRegularRing`
(existing node `lem-weil-pbc-polynomial-ring-field-regular-ring`). The planned
`lem-weil-pbc-polynomial-ring-smooth` and `lem-weil-pbc-regular-ring-smooth-ascent` steps are
bypassed below the unit level. No unit statement or realized unit step was bypassed.

Removed the direct imports `Sheaf.RingTheory.RegularSequencePolynomialVariables`,
`Sheaf.RingTheory.RegularSequencePowers`, and `Sheaf.AlgebraicGeometry.Ogoma` from the item;
they are used in the new proved rescaling module and remain in the item's import closure.
Their nodes are retained through the new node. The former direct dependency
`lem-weil-pbc-field-regular-ring` is supplied by Mathlib as the base-ring instance
prerequisite of `lem-weil-pbc-polynomial-ring-field-regular-ring`, rather than a separate
step. Thus every removed old direct proof dependency is accounted for.

A source-import comparison before and after this delivery finds the following 57 project
modules absent from this item's import closure. This concerns this item's route; other target
paths can still reach them.

- `Sheaf.Algebra.Category.ModuleCat.FilteredColimitFlat`
- `Sheaf.RingTheory.AdicCompletionNoetherian`
- `Sheaf.RingTheory.CoefficientResidueSection`
- `Sheaf.RingTheory.CoefficientSubringOfPrincipalSource`
- `Sheaf.RingTheory.CohenCompletionDVR`
- `Sheaf.RingTheory.CohenRing`
- `Sheaf.RingTheory.CohenRingLiftToCompleteLocal`
- `Sheaf.RingTheory.CohenRingModPowFlat`
- `Sheaf.RingTheory.CohenRingModPowFormallySmooth`
- `Sheaf.RingTheory.CohenRingModPowFormallySmoothCore`
- `Sheaf.RingTheory.CohenRingModPowFormallySmoothExplicit`
- `Sheaf.RingTheory.CohenRingModPowFormallySmoothStep`
- `Sheaf.RingTheory.CohenRingsExist`
- `Sheaf.RingTheory.CompatibleRingTowerRecursion`
- `Sheaf.RingTheory.CompletionDimension`
- `Sheaf.RingTheory.CompletionDimensionEquality`
- `Sheaf.RingTheory.CompletionRegularLocal`
- `Sheaf.RingTheory.Depth`
- `Sheaf.RingTheory.ExistsCoefficientSubring`
- `Sheaf.RingTheory.ExistsLiftOfFieldCharP`
- `Sheaf.RingTheory.FiniteModuleComplete`
- `Sheaf.RingTheory.FirstOrderPowerSeriesComparison`
- `Sheaf.RingTheory.FlatLocalExtensionGivenResidueField`
- `Sheaf.RingTheory.FlatLocalMonogenicExtension`
- `Sheaf.RingTheory.FlatLocalTowerDirectLimit`
- `Sheaf.RingTheory.FormallySmoothAdic`
- `Sheaf.RingTheory.FormallySmoothAdicCompletion`
- `Sheaf.RingTheory.FormallySmoothAdicDiagonalStep`
- `Sheaf.RingTheory.FormallySmoothAdicLiftIntoComplete`
- `Sheaf.RingTheory.FormallySmoothAdicPowerSeriesMap`
- `Sheaf.RingTheory.FormallySmoothAdicQuotientGrid`
- `Sheaf.RingTheory.H1CotangentFiniteSubfields`
- `Sheaf.RingTheory.LocalFirstOrderCoordinates`
- `Sheaf.RingTheory.ModPowFormallySmoothReduction`
- `Sheaf.RingTheory.PowerSeriesCombinedIdealCoefficients`
- `Sheaf.RingTheory.PowerSeriesCompleteOverCompleteBase`
- `Sheaf.RingTheory.PowerSeriesFieldCohenRegularComplete`
- `Sheaf.RingTheory.PowerSeriesFirstOrderCoordinates`
- `Sheaf.RingTheory.PowerSeriesOntoCompletion`
- `Sheaf.RingTheory.PowerSeriesQuadraticIdeal`
- `Sheaf.RingTheory.PowerSeriesQuotientVariables`
- `Sheaf.RingTheory.RegularLocalOfFlatWithRegularClosedFiber`
- `Sheaf.RingTheory.RegularLocalOfFormallySmoothAdic`
- `Sheaf.RingTheory.RegularRingSmoothAscent`
- `Sheaf.RingTheory.RegularityRkGoesUp`
- `Sheaf.RingTheory.ResidueFieldTowerSystem`
- `Sheaf.RingTheory.SerreConditions`
- `Sheaf.RingTheory.SmoothFibreRegularLocal`
- `Sheaf.RingTheory.SmoothOverFieldRegularLocal`
- `Sheaf.RingTheory.SubsingletonH1CotangentOfCharP`
- `WeilConjectures.Mathlib.Algebra.Category.AlgCat.FilteredColimits`
- `WeilConjectures.Mathlib.Algebra.Category.CommAlgCat.Basic`
- `WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct`
- `WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`
- `WeilConjectures.RingTheory.ProEtale.FaithfullyFlat`
- `WeilConjectures.RingTheory.ProEtale.Ind`

The corresponding 55 node records no longer needed on this item's route are:

- `def-weil-pbc-cohen-ring`
- `def-weil-pbc-depth`
- `def-weil-pbc-formally-smooth-adic`
- `def-weil-pbc-serre-conditions-rk-sk`
- `lem-weil-pbc-adic-completion-noetherian`
- `lem-weil-pbc-coefficient-residue-section`
- `lem-weil-pbc-coefficient-subring-principal-source`
- `lem-weil-pbc-cohen-coefficient-ring-exists`
- `lem-weil-pbc-cohen-completion-dvr`
- `lem-weil-pbc-cohen-ring-lift-complete-local`
- `lem-weil-pbc-cohen-ring-mod-pn-formally-smooth`
- `lem-weil-pbc-cohen-ring-mod-pn-formally-smooth-core`
- `lem-weil-pbc-cohen-ring-mod-pn-formally-smooth-explicit`
- `lem-weil-pbc-cohen-ring-mod-pn-formally-smooth-step`
- `lem-weil-pbc-cohen-ring-mod-pow-flat`
- `lem-weil-pbc-cohen-rings-exist`
- `lem-weil-pbc-completion-dimension`
- `lem-weil-pbc-completion-dimension-eq`
- `lem-weil-pbc-completion-regular-local`
- `lem-weil-pbc-field-char-p-h1-cotangent-vanishing`
- `lem-weil-pbc-field-char-p-nilpotent-lifting`
- `lem-weil-pbc-filtered-colimit-flat-modules`
- `lem-weil-pbc-finite-module-complete-over-complete-noetherian`
- `lem-weil-pbc-first-order-power-series-comparison`
- `lem-weil-pbc-flat-algebra-faithfully-flat-descent`
- `lem-weil-pbc-flat-colimit-presentation-same-universe`
- `lem-weil-pbc-flat-local-extension-given-residue-field`
- `lem-weil-pbc-flat-local-tower-direct-limit`
- `lem-weil-pbc-flat-over-regular-with-regular-fibre`
- `lem-weil-pbc-flat-ring-map-iff-ind-flat`
- `lem-weil-pbc-fs-adic-compatible-quotient-grid`
- `lem-weil-pbc-fs-adic-completion`
- `lem-weil-pbc-fs-adic-diagonal-step`
- `lem-weil-pbc-fs-adic-field-regular-local`
- `lem-weil-pbc-fs-adic-lift-into-complete`
- `lem-weil-pbc-fs-adic-power-series-comparison-map`
- `lem-weil-pbc-h1-cotangent-finite-subfields`
- `lem-weil-pbc-local-first-order-coordinates`
- `lem-weil-pbc-mod-pow-formally-smooth-reduction`
- `lem-weil-pbc-power-series-combined-ideal-coefficients`
- `lem-weil-pbc-power-series-complete-over-complete-base`
- `lem-weil-pbc-power-series-field-cohen-regular-complete`
- `lem-weil-pbc-power-series-first-order-coordinates`
- `lem-weil-pbc-power-series-kernels`
- `lem-weil-pbc-power-series-onto-completion`
- `lem-weil-pbc-power-series-quadratic-ideal`
- `lem-weil-pbc-power-series-quotient-equivalence`
- `lem-weil-pbc-power-series-quotient-variables`
- `lem-weil-pbc-regular-ring-smooth-ascent`
- `lem-weil-pbc-regularity-rk-goes-up`
- `lem-weil-pbc-residue-field-tower-system`
- `lem-weil-pbc-smooth-fibre-regular-local`
- `lem-weil-pbc-smooth-over-field-regular-local`
- `new-compatible-ring-tower-recursion`
- `new-flat-local-monogenic-extension`

## Where the brief, the DAG or earlier work was wrong

No false statement or required interface change was found. The DAG's smooth-ascent argument
for polynomial regularity was unnecessary; the existing Mathlib polynomial regular-ring
instance is the shorter route. The remaining plan, including the finite rescaling induction,
is implemented without adding holes.

The local checkout does not contain `literature/stacks-project/smoothing.tex`. The source was
read at https://stacks.math.columbia.edu/tag/07FJ, specifically the justifications of items
10 and 12. The source's item 11 writes `t_1,...,t_m` although its later formulas use d
variables; the unchanged Lean statement correctly uses `Fin d`. Its justification of item 10
also has a harmless switch of the ambient ring in the prose; the numerator selection here is
performed explicitly in the source polynomial ring.

The empty-family case is covered by both proofs: cardinality-zero minimal generators give
zero source maximal ideal, its mapped span gives zero target maximal ideal, and the rescaling
induction starts at zero without selecting an index. The generic rescaling theorem needs
Noetherianity for the finite quotient in Ogoma; it assumes it explicitly. Factors are chosen
outside the prime, ensuring every localized factor is a unit.

## New nodes

`lem-weil-pbc-polynomial-coefficient-kernel-rescaling` states the intrinsic coefficient
rescaling argument for a Noetherian ring and a prime-local regular family, with no target
algebra or flat chart. Its Lean theorem is fully proved in
`lean/Sheaf/RingTheory/PolynomialCoefficientKernelRescaling.lean`. The node records the
unit-invariance, powered-prefix localization, Ogoma application, and finite-induction steps.
Searches used LeanSearch (unavailable, HTTP internal-server error), Lean Finder, Loogle,
and grep; the blueprint searches found no matching imported statement. No change record
is needed because existing interfaces are unchanged.


## Second reading by K4

1. PASS: Compared the original module with the repository by diff and compared the complete
   existing theorem signature byte for byte. Its hypotheses, conclusion, universes, visibility,
   public imports, and existing docstring are unchanged. There are no definition changes or
   forced adaptations. The original node changes only proof, proof_deps, and proof_origin.
2. PASS: Read every proof in both delivered modules. The source dimension is obtained from
   flat going-down and the zero closed-fibre maximal ideal; numerator selection uses a
   minimal finite generating set and unit denominators. The helper identifies the polynomial
   quotient localization canonically, proves injectivity modulo the powered prefix, applies
   Ogoma with exponent one, and updates only the current coefficient. No data is chosen from
   an unproved existence theorem. There is no sorry, axiom, unsafe, opaque, implemented_by,
   or extern in the delivered Lean. The delivery dry run compiled both modules, probed all declarations for disallowed
   axioms, and passed preflight (OK; CODEX because of the new module and node).
3. PASS: No statement is split off with sorry. The new fully proved rescaling theorem is
   strictly the coefficient-kernel part of the argument: it assumes no target algebra, flat
   chart, or parameter-generation condition and asserts none of those conclusions. Read
   Stacks Tag 07FJ, items 10 and 12 and their justifications, against the statements and
   proofs. Checked d=0 (empty factors, vacuous kernel conditions), d=1 (empty prefix, Ogoma
   on the polynomial ring), e=1, and the exclusion of factors in p. Noetherianity supplies
   finite generation for Ogoma; all later coefficient changes leave earlier prefix ideals
   and scalars identical. Independent Loogle search `IsSMulRegular, IsLocalizedModule`,
   Lean Finder search for annihilator equalization in Noetherian polynomial quotients,
   msearch grep for localized annihilators and square kernels, and rg searches through
   lean/Sheaf and lean/WeilConjectures found no replacement for the combined rescaling
   theorem. The localized regularity lemmas found are weaker ingredients already used.
4. PASS: The proof uses the direct Mathlib polynomial regular-ring instance and the existing
   regular-local generators, polynomial variables, powers, and Ogoma theorems. All old
   proof dependencies removed from the direct route are accounted for under No longer
   needed, including those moved beneath the new helper. Read sk-thm-p1.realized: neither
   the replaced smooth-ascent route nor the extracted rescaling step is a realized unit
   statement or step. The unit route is preserved. Removed the three redundant imports
   noted above; retained the genuinely used localization and field-ULift imports.
5. PASS: Opened both node records and checked their statements against the Lean signatures.
   For each record proof_deps is exactly the union of the proof-step uses. The new node has
   its source, complete argument, creation/provenance, blueprint ancestry, chapter/unit,
   search records, and verbatim Lean statement. The original node records the actual
   dimension, numerator, rescaling, and target regularity argument.

Second reading changed only three redundant Mathlib imports (two private imports in
the original module and one public import in the new helper) and this report's
accounting of removed direct dependencies; no proof or statement repair was necessary.

Independent explicit `#print axioms` checks through lcompile.py also confirmed that both
public theorems depend exactly on propext, Classical.choice, and Quot.sound, without sorryAx.
