## What changed

Proved `AlgebraicGeometry.Etale.supportedProductLocalization_naturality` without changing
its statement or any public construction. The proof combines naturality of the uniquely
specified derived coefficient tensor comparison, naturality of both evaluation counits,
and naturality of the supported-coefficient adjunction. Private proved helpers express
bifunctor composition and adjunction naturality before specializing the scheme arguments;
this avoids repeatedly unfolding the derived monoidal sheaf instances.

The assigned module compiled through `lcompile.py` after removing unused proof imports
(exit code 0, approximately 13 seconds). This packet changes only this module and its
proof imports. It implements the coefficient-morphism portion of the existing node's
step 11; the remaining mathematical route and all public signatures are unchanged.

## Proved and sorry left

Closed 1 of the 6 original holes:

- `AlgebraicGeometry.Etale.supportedProductLocalization_naturality`.

Added 0 holes and split off 0 statements. All private helpers are proved.
The following 5 original holes remain untouched:

- `AlgebraicGeometry.Etale.supportedProductLocalizationFirst_map`.
- `AlgebraicGeometry.Etale.supportedProductLocalizationSecond_map`.
- `AlgebraicGeometry.Etale.supportedProductLocalization_openFirst`.
- `AlgebraicGeometry.Etale.supportedProductLocalization_openSecond`.
- `AlgebraicGeometry.Etale.supportedProductLocalization_openRows`.

## No longer needed

The coefficient naturality proof needs no additional imports: its coefficient comparison
and adjunction API are already available through the retained public imports. Removed
the following unused private proof imports:

- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`.
- `Mathlib.AlgebraicGeometry.Fiber`.
- `WeilConjectures.AlgebraicGeometry.TensorPullback`.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`.
- `WeilConjectures.Topology.InverseImageModule`.
- `Mathlib.Algebra.Category.Ring.Colimits`.
- `Mathlib.Topology.Sheaves.Functors`.
- `WeilConjectures.AlgebraicGeometry.Picard.Defs`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`.
- `WeilConjectures.Algebra.Homology.HomComplex`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`.
- `Sheaf.Paper.EtaleKFlatCriteria`.
- `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal`.
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`.
- `Sheaf.AlgebraicGeometry.SupportRestrictionTriangle`.
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`.
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`.
- `WeilConjectures.AlgebraicGeometry.GlobalSectionsStalkComparison`.
- `WeilConjectures.SixFunctors.OpenClosed.Exact`.
- `WeilConjectures.SixFunctors.Finite.Stalk`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`.
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.
- `Mathlib.CategoryTheory.Sites.Point.Basic`.
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`.
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`.
- `Sheaf.AlgebraicGeometry.NormalizedSupportTriangle`.
- `Sheaf.AlgebraicGeometry.SupportedExteriorProduct`.
- `Sheaf.Paper.ExternalRHomConePairing`.
- `Sheaf.SixFunctors.OpenClosedFlatness`.

No DAG node or module is withdrawn. The localization-boundary and open-restriction
portions remain unfinished, so their planned dependencies are not claimed to be obsolete.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy was found. For coefficient naturality alone, the existing
coefficient-comparison condition and adjunction naturality suffice directly; no new
Hom-complex or cone comparison is needed for that portion of step 11.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
