# WeilConjectures.IsRationalFiniteProjectiveTerm

## Reason

Restore the module quarantined by upstream sync a762b776d, without changing the
site-perfectness predicates or removing any archived declaration. The archived
source fails at line 122: synthesis of `Quiver (ScalarLocalization ...
(DerivedCategory (SheafOfModules (completedIntegralCoefficientSheafUnrestricted ...))) ...)`.
The underscore in the degree-zero functor lets elaboration infer the module category
from the unit sheaf. It then seeks scalar-localization instances through that
presentation instead of the recorded `integralTowerModules` category.

Specify `integralTowerModules l E Y` as the category of all four degree-zero functors.
This is the same category, definitionally, and retains the same products, unit,
localization, splitting arrows, and retraction identity. No hypothesis, universe,
public import, declaration signature, or mathematical predicate changes. The repair
adds no theorem and no hole. Target meanings do not change.

## Old

```lean
noncomputable def IsRationalFiniteProjectiveTerm (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u}) (M : integralTowerModules l E Y) : Prop :=
  ∃ m : ℕ,
    ∃ i : (ScalarLocalization.mk ((DerivedCategory.singleFunctor _ 0).obj M) :
        sitePerfectRationalAmbient l E Y) ⟶
      ScalarLocalization.mk ((DerivedCategory.singleFunctor _ 0).obj
        (∏ᶜ fun _ : Fin m ↦
          SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))),
    ∃ p : ScalarLocalization.mk ((DerivedCategory.singleFunctor _ 0).obj
        (∏ᶜ fun _ : Fin m ↦
          SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))) ⟶
      (ScalarLocalization.mk ((DerivedCategory.singleFunctor _ 0).obj M) :
        sitePerfectRationalAmbient l E Y),
    i ≫ p = 𝟙 _
```

## New

```lean
noncomputable def IsRationalFiniteProjectiveTerm (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u}) (M : integralTowerModules l E Y) : Prop :=
  ∃ m : ℕ,
    ∃ i : (ScalarLocalization.mk
        ((DerivedCategory.singleFunctor (integralTowerModules l E Y) 0).obj M) :
        sitePerfectRationalAmbient l E Y) ⟶
      ScalarLocalization.mk ((DerivedCategory.singleFunctor (integralTowerModules l E Y) 0).obj
        (∏ᶜ fun _ : Fin m ↦
          SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))),
    ∃ p : ScalarLocalization.mk ((DerivedCategory.singleFunctor (integralTowerModules l E Y) 0).obj
        (∏ᶜ fun _ : Fin m ↦
          SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))) ⟶
      (ScalarLocalization.mk
        ((DerivedCategory.singleFunctor (integralTowerModules l E Y) 0).obj M) :
        sitePerfectRationalAmbient l E Y),
    i ≫ p = 𝟙 _
```

## Users

`python3 tools/downstream.py Sheaf.Paper.SitePerfectComplex --allow-missing
--uses IsRationalFiniteProjectiveTerm` reports zero live downstream modules: this
item and its direct consumers are quarantined. Their archived imports are retained;
absence from the live tree is not treated as withdrawal. The following complete
list of direct archived importers was checked. None requires an adaptation because
the category annotation preserves the predicate definitionally. No consumer file
is changed or withdrawn by this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SitePerfectComplex | E3 | Restore all ten declarations; repair four category arguments. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | quarantined; not adapted | Identical public interface and predicate meaning. |
| Sheaf.Paper.FiniteTorStability | quarantined; not adapted | Identical public interface and predicate meaning. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | quarantined; not adapted | Identical public interface and predicate meaning. |
| Sheaf.Paper.HomFiniteProjective | quarantined; not adapted | Identical public interface and predicate meaning. |
| Sheaf.Paper.InternalHomPullback | quarantined; not adapted | Identical public interface and predicate meaning. |
| Sheaf.Paper.RationalHomScalarTranspose | quarantined; not adapted | Identical public interface and predicate meaning. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | quarantined; not adapted | Identical public interface and predicate meaning. |
| Sheaf.Paper.SitePerfectCoefficientDual | quarantined; not adapted | Identical public interface and predicate meaning. |
| Sheaf.Paper.SitePerfectDualizableHom | quarantined; not adapted | Identical public interface and predicate meaning. |
| Sheaf.Paper.SitePerfectRationalBidual | quarantined; not adapted | Identical public interface and predicate meaning. |
| Sheaf.SixFunctors.InternalHomPullback | quarantined; not adapted | Identical public interface and predicate meaning. |
| Sheaf.SixFunctors.RationalRetractEvaluation | quarantined; not adapted | Identical public interface and predicate meaning. |

## Status

landed 20261021T120346-L-3829368 2026-10-21 (merge of deliver/E3/Sheaf.Paper.SitePerfectComplex)
