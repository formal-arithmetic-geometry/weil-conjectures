## What changed

Proved all five original holes of `Sheaf.AlgebraicGeometry.SupportLocalizationTriangle`. Constructed the sheaf adjunction by kernel factorization and closed full faithfulness, derived it on D⁺, and proved the specified counit and unit identities. Proved resolution independence, functoriality, and étale base change including the boundary through the canonical mate and Mathlib short-exact-sequence triangles. The fixed cone, boundary sign, and every existing signature remain unchanged.

Factored the three model-comparison definition bodies through two generic, explicit comparison definitions in the same module. This preserves their values by definitional equality and avoids repeated expensive conversion. Change record: `coord/changes/A8-support-model-comparison-factoring.md`. The unclaimed `SupportTriangleConstruction` factors the identical explicit triangle formula through the generic constructor. The boundary, signs and inverse are unchanged by reduction; no consumer is adapted.

## Proved and sorry left

Closed all 5 original holes:

- `AlgebraicGeometry.ProEtale.supportModelKInjective`.
- `AlgebraicGeometry.ProEtale.supportOpenModelKInjective`.
- `AlgebraicGeometry.ProEtale.supportInjectiveConeDistinguished`.
- `AlgebraicGeometry.ProEtale.supportResolutionCone`.
- `AlgebraicGeometry.ProEtale.supportLocalizationTriangle`.

Validation: the delivered set compiled (construction 7.7 seconds; localization 52.2 seconds). Unchanged consumers SupportTriangleCompatibility and RetractedSupportLocalizationComparison compiled. ClosedSupportExceptionalComparison exceeded 60 seconds both against this overlay and unchanged against the shared baseline; no new compiler diagnostic or consumer adaptation is introduced.

Holes remaining in delivered Lean files: 0. Holes added: 0. Split off: 0. The proof uses the existing stated library dependencies, which may themselves still contain sorry.

## No longer needed

Removed redundant direct proof imports; the interfaces actually used remain available through the retained imports:

- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.AlgebraicGeometry.PurSupportExact`.
- `Sheaf.AlgebraicGeometry.EtaleComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`.
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`.
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`.
- `Mathlib.CategoryTheory.Adjunction.Unique`.
- `Mathlib.Algebra.Homology.HomotopyCategory.ShortExact`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtalePairFlasque`.

No whole module is withdrawn. The direct injective replacement avoids the abstract derived-Hom lift for the resolution-arrow auxiliary clause; K-injective derived Hom remains necessary for canonicality. The declared mathematical dependency route and all blueprint unit steps are retained. No mathematical node is claimed pruned solely because its direct import is redundant.

## Where the brief, the DAG or earlier work was wrong

No statement fault found. The cone formula agrees with Mathlib triangleOfSES, including its signed boundary; Mathlib's exact-functor transport proves the boundary compatibility. The prior report saying the final adjunction and compatibility clause was open is superseded: those proofs are now complete. The expanded comparison formulas caused repeated expensive conversion, resolved by definitionally equal generic factoring.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
