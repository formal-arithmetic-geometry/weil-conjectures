# AlgebraicGeometry.Scheme.finiteCoefficient_constructibleDerived_origin_presentation

## Reason

The item Sheaf.Paper.DerivedPullbackTensorIso was quarantined on 2026-10-27 because
its import closure reached Sheaf.AlgebraicGeometry.SfP1ProjectionTraceFalseTail.
Every source-import path from the archived item to that module crosses the private
Perfect import in Sheaf.Paper.FiniteCoefficientDerivedOriginPresentation.
That import is used only for boundedConstructible_of_homology. Its finite-truncation
proof needs the exact comparison, its bounded-below Hom bijection and constructible
étale objects, all supplied by the smaller Derived.Constructible import.

The companion module was unclaimed when inspected. The repair replaces that private
import with Derived.Constructible and proves the two required intermediate facts by
private helpers, without changing any existing public declaration or public import.
The upstream Perfect module and all its declarations remain untouched.

## Old

Private import:
```lean
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
```
The proof calls ProEtale.DerivedCategory.boundedConstructible_of_homology.
Public signature:
```lean
theorem finiteCoefficient_constructibleDerived_origin_presentation
    (X : Scheme.{u}) [IsNoetherian X]
    (B : Type (u + 1)) [CommRing B] [Finite B]
    (e : adicLisseConstantRing X B ≅ AdicCoefficients.coefficientRing X B)
    (K : DerivedCategory (pbcModules X (AdicCoefficients.coefficientRing X B)))
    (hconstructible : ∀ q : ℤ, IsConstructibleProEtaleCoefficientModuleSheaf X B
      ((pbcRestrict e.hom).obj ((DerivedCategory.homologyFunctor _ q).obj K)))
    (a b : ℤ) (_hab : a ≤ b)
    (hbounded : ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) :
    letI : TopologicalSpace B := ⊥
    letI : DiscreteTopology B := discreteTopology_bot _
    ∃ C : CochainComplex (ProEtale.FiniteCoefficientModules X B) ℤ,
      ProEtale.isBoundedConstructibleFiniteCoefficient X B (DerivedCategory.Q.obj C) ∧
      Nonempty (DerivedCategory.Q.obj
        (((SheafOfModules.restrictScalars
          (AdicCoefficients.finiteRingComparison X B).hom).mapHomologicalComplex
            (.up ℤ)).obj C) ≅ K)
```

## New

Private import:
```lean
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
```
The proved private helpers origin_boundedConstructible_isTriangulated and
origin_boundedConstructible_of_homology give the same bounded-cohomology argument.
The first lifts arrows between étale origins by the derived comparison Hom bijection
and transports their cones, shifts and zero. The second applies
DerivedCategory.prop_of_bounded and the single-complex comparison.
Public signature (verbatim unchanged):
```lean
theorem finiteCoefficient_constructibleDerived_origin_presentation
    (X : Scheme.{u}) [IsNoetherian X]
    (B : Type (u + 1)) [CommRing B] [Finite B]
    (e : adicLisseConstantRing X B ≅ AdicCoefficients.coefficientRing X B)
    (K : DerivedCategory (pbcModules X (AdicCoefficients.coefficientRing X B)))
    (hconstructible : ∀ q : ℤ, IsConstructibleProEtaleCoefficientModuleSheaf X B
      ((pbcRestrict e.hom).obj ((DerivedCategory.homologyFunctor _ q).obj K)))
    (a b : ℤ) (_hab : a ≤ b)
    (hbounded : ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) :
    letI : TopologicalSpace B := ⊥
    letI : DiscreteTopology B := discreteTopology_bot _
    ∃ C : CochainComplex (ProEtale.FiniteCoefficientModules X B) ℤ,
      ProEtale.isBoundedConstructibleFiniteCoefficient X B (DerivedCategory.Q.obj C) ∧
      Nonempty (DerivedCategory.Q.obj
        (((SheafOfModules.restrictScalars
          (AdicCoefficients.finiteRingComparison X B).hom).mapHomologicalComplex
            (.up ℤ)).obj C) ≅ K)
```

## Users

The downstream search reports two textual users of the declaration (including its
own declaration), and direct-import search adds SingleDegreeUniformReconstruction.
All existing public signatures, definitions, attributes and public imports are identical.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteCoefficientDerivedOriginPresentation | unclaimed | Private proof import and proved private helpers only; no holes. |
| Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity | unclaimed | Direct importer and theorem user; unchanged, compile checked in the sandbox. |
| Sheaf.Paper.SingleDegreeUniformReconstruction | unclaimed | Direct `import all`; unchanged, compile checked in the sandbox. |
| Sheaf.Paper.DerivedPullbackTensorIso | J2 | Restored from its quarantine archive; redundant private IntegralSystemReductionFullyFaithful import removed, since IntegralPullbackComposition publicly reexports it. |

No public interface changes and no target meaning changes occur. The two unchanged
importer copies are removed from the sandbox after validation, so they are not delivered.

## Status

landed 20261027T131456-L-2941093 2026-10-27 (merge of deliver/J2/Sheaf.Paper.DerivedPullbackTensorIso)
