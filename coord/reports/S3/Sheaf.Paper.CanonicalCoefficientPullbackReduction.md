## What changed

Proved `WeilConjectures.canonicalCoefficientModelMaps_isIso` in
`Sheaf.Paper.CanonicalCoefficientPullbackReduction`. The integral and finite regular
unit maps are sectionwise inverse coefficient isomorphisms. The canonical reduction
is identified with regular tensor multiplication by the normalized scalar adjunction.
The finite tensor-unit comparison is conjugated to the identity on the regular complex,
using its prescribed value on sections and adjunction naturality.

The proof reuses proved private helpers through `import all
Sheaf.Paper.ConstantWeilStructure`. All original public signatures, public imports,
definition bodies and docstrings are retained. New helpers are private and proved.
Local irreducibility keeps the scalar constructions and comparison maps from expanding
during proof elaboration; explicit endpoint types on the two private finite-complex
isomorphisms avoid expanding equivalent coefficient-category presentations.

Single-file compilation through `lcompile.py` passed without warnings in 48.9 seconds.
The delivery tool additionally checks every declaration's axioms and the remaining hole.

## Proved and sorry left

Closed 1 of the 2 original holes:

- `WeilConjectures.canonicalCoefficientModelMaps_isIso`, including the integral unit,
  finite unit, canonical reduction complex, and specified finite kappa isomorphisms.

One original hole remains:

- `WeilConjectures.canonicalCoefficientPullbackReduction`
  (`lem-pod-canonical-coefficient-pullback-reduction`).

No holes added; no statements split off. The main theorem is unchanged and remains
exactly `:= by sorry`. Its original complete proof docstring and nine-step DAG plan
are retained. Unvalidated integral/projection proof drafts are retained only in the
sandbox scratchpad, outside the delivery.

## No longer needed

The proved model-map theorem uses the regular complex directly and does not need
an arbitrary K-flat resolution, a general strict derived-limit comparison or a second
completeness argument. Removed direct proof imports:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`.
- `Sheaf.Paper.IntegralOperationsWellDefined`.
- `Sheaf.CategoryTheory.StrictRoosComparison`.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`.
- `Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`.
- `Sheaf.Paper.ConstantCoefficientScalarNormalization`.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`.

No module is withdrawn and no DAG dependency of the remaining main theorem is
pruned. These imports can still be transitive dependencies of the reused constructions;
this report makes no claim that they leave the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The regular coefficient identifications already constructed and proved privately in
`ConstantWeilStructure` supply the model-map argument. Reconstructing the general
resolution machinery is unnecessary for that theorem.

The resumed sandbox included a full unvalidated draft. Its finite triangle initially
unfolded equivalent coefficient-category presentations during a `change`. Giving
private comparison isomorphisms explicit endpoints and using component equations
resolved this: the repaired finite triangle compiled, and the complete model-map
packet then compiled without warnings. The full integral/projection draft did not
pass the 60-second check; it is not included or claimed proved. Attempts to change
local derived-category instance selection were reverted because they disrupted
compatibility with the published operations. No mathematical statement was changed.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
