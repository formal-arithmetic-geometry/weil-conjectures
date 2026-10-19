## Worker report

The module `lean/Sheaf/Paper/SfRationalLocalGlobalPowerTorsion.lean` states
`WeilConjectures.sfRationalLocalGlobalPowerTorsion`.  It uses the recorded completed
coefficient construction and the small pro-etale site, and expresses the derived
category as `DerivedCategory (integralTowerModules l E X)`.  A finite cover is a
`Fin n`-indexed family `U` with `(Scheme.ProEt.topology X).CoversTop U`; `n = 0`
is therefore permitted.  The local object is the termwise slice restriction
`(SheafOfModules.overFunctor R (U j)).mapDerivedCategory.obj C` in the derived
category of `R.over (U j)`-modules.  The hypothesis `hzero` says that its image
under `ScalarLocalization.localization` at
`Padic.coefficientExtensionUniformizer l E` is a zero object.  The explicit
`Linear` binders render the stated O_E-linearity of the global and slice derived
categories.  The conclusion is the existence of one natural-number exponent
whose scalar endomorphism maps to zero under every
`DerivedCategory.homologyFunctor`; this is precisely
`varpi_E^N H^d(C)=0` as a coefficient-module sheaf.

The local category uses the recorded `SheafOfModules.over` construction for
`def-pur-localized-ringed-site`; the module adds only the standard additive and
finite-limit/finite-colimit instances needed by `mapDerivedCategory`, all obtained
from `ringedOverFunctor_exactGeneral`.  The coefficient ring and uniformizer are
`Padic.coefficientExtensionIntegers l E` and
`Padic.coefficientExtensionUniformizer l E`, the recorded valuation ring and
chosen uniformizer.

Dependencies used are:

- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, declaration
  `WeilConjectures.completedIntegralCoefficientSheafUnrestricted` (through its
  published coefficient modules);
- `Mathlib.AlgebraicGeometry.Sites.Proetale`, declaration
  `AlgebraicGeometry.Scheme.ProEt`;
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`, declaration
  `SheafOfModules.over`/`SheafOfModules.overFunctor`;
- `Sheaf.CategoryTheory.RingedSiteModules`, declaration
  `CategoryTheory.ringedSiteModules` (via `integralTowerModules`);
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, declarations
  `DerivedCategory` and `HasDerivedCategory`;
- `Sheaf.CategoryTheory.ScalarLocalization`, declarations
  `CategoryTheory.ScalarLocalization` and `ScalarLocalization.localization`.

The proof docstring records the three source steps: take the maximum local
exponent (zero for the empty cover), use exact restriction and cohomology
functoriality, and apply the cover-local isomorphism criterion to the image of
the scalar endomorphism.  Edge cases checked were `n = 0`, a one-member cover,
local exponent zero, `C = 0`, and a zero cohomology object.  The statement module
contains only the named theorem with `sorry`.

Searches made:

- `msearch.py ... leanfinder "finite pro-etale cover scalar localization uniform power annihilates cohomology sheaves"`: hits were localization/étale algebra lemmas and no derived sheaf torsion statement.
- `msearch.py ... loogle "DerivedCategory.homologyFunctor, ScalarLocalization.localization, SheafOfModules.overFunctor"`: no exact match (`ScalarLocalization.localization` is project-defined).
- `msearch.py ... grep "uniform.*power|scalar.*localiz" CategoryTheory/Sites`: no match.
- `rg` over `WeilConjectures/` and project `lean/Sheaf/`: found the related
  `SfRationalBoundedConeTorsion` theorem, but it concerns bounded constructible
  objects and does not state finite-cover local-to-global torsion; no duplicate
  declaration of this item was found.

No new DAG nodes or dependency repair modules were needed.  No
`STATEMENT-DISPUTED` issue was found.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
