## What changed

Proved the four existing holes in `Sheaf.Paper.IntegralQuotientCoefficients`, preserving
all declaration signatures, definitions and public imports. Continuity uses the existing
uniformizer-coset basis. Multiplication linearity is checked on sectionwise pure tensors
and transported by the monoidal inverse image. Projection linearity is multiplication
preservation of the coefficient ring map. Transition compatibility is pointwise reduction.
Updated the existing node's proof and dependency records to match these proofs.

Added only private imports of `Sheaf.NumberTheory.Padics.IntegersCosetBasis`,
`Mathlib.Topology.LocallyConstant.Basic`, and
`WeilConjectures.CategoryTheory.Sites.MonObj`.
The final module compiles without errors or warnings through lcompile.py (10 seconds).

## Proved and sorry left

Closed 4 of 4 original holes, all attached to
`def-sfb-integral-quotient-coefficients`:

- `AlgebraicGeometry.ProEtale.IntegralQuotient.reduction_continuous`
- `AlgebraicGeometry.ProEtale.IntegralQuotient.multiplication_linear`
- `AlgebraicGeometry.ProEtale.IntegralQuotient.projection_linear`
- `AlgebraicGeometry.ProEtale.IntegralQuotient.reduction_comp`

No holes remain in the item. No holes added; no statements split off.
The argument works for every positive quotient level, including n = 0, equal transition
levels, arbitrary schemes and empty profinite test objects. It uses the existing arithmetic
and categorical APIs; no assumption about properness or boundedness is introduced.

## No longer needed

Removed the following unused private imports from this module:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Sheaf.Algebra.Homology.FlatScalarCyclicResolution`
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`
- `Sheaf.Paper.SectionDerivedPushpullNormalization`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`

The corresponding node attachments are:

- `lem-pe-internal-section-tensor-comparison` (`Sheaf.CategoryTheory.InternalSectionTensorComparison`)
- `lem-weil-l-adic-extension-integers-dvr` (`Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`)
- `lem-sfb-flat-scalar-cyclic-resolution` (`Sheaf.Algebra.Homology.FlatScalarCyclicResolution`)
- `lem-sfb-successive-derived-quotient-normalization` (`Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`)
- `lem-sfb-ringed-derived-monoidal-comparisons` (`Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`)
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` (`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`)
- `def-weil-pbc-completed-constant-complex-base` (`Sheaf.Paper.CompletedConstantSheafReduction`)
- `def-weil-pbc-projection-formula-map` (`Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`)
- `lem-weil-pbc-completed-constant-sheaf-reduction` (`Sheaf.Paper.CompletedConstantSheafReduction`)
- `def-pbc-successive-derived-scalar-normalization-data` (`Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`)
- `lemma-weil-pbc-projection-formula-base-change-naturality` (`Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`)
- `lem-pur-sheaf-ring-derived-coefficient-adjunction` (`Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`)
- `lem-pd-section-derived-pushpull-normalization` (`Sheaf.Paper.SectionDerivedPushpullNormalization`)

These imports are unnecessary for this item's proofs; no claim is made that their modules
are globally unused. No modules or declarations are withdrawn. The original node had no
proof dependencies to remove. Its statement dependencies and the blueprint unit route stay
unchanged.

## Where the brief, the DAG or earlier work was wrong

The definition node had an empty proof plan despite four named proof obligations. Its
large private import list described derived comparison results not needed to construct
these elementary coefficient maps. The delivery supplies the actual argument and trims
that proof context. No mathematical statement or definition repair was needed.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
