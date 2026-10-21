# WeilConjectures.point_fibre_equivalence

## Reason

The existing theorem is proved from separate integral, rational and common-stage
components. Static preflight classifies the new section, variable, open, local attribute
and elaboration-option commands around private proof helpers as an interface change.
This record makes those commands reviewable. All eight helper typeclass registrations
in the existing module are local. Existing public instances, signatures, data definitions
and public imports are unchanged. The required unit-route private import of
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` is retained. No target meaning changes,
and no consumer adaptation is required.

## Old

The existing theorem signature, verbatim:

```lean
theorem point_fibre_equivalence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (E : Padic.FiniteCoefficientFields l Ω) (n : ℕ) (hn : 1 ≤ n) :
    (pointFiniteFibre D l hl E.val n hn).IsEquivalence ∧
    (pointIntegralFibre D l hl E.val).IsEquivalence ∧
    (pointRationalFibre D l hl E.val).IsEquivalence ∧
    (pointQbarFibre D l hl Ω).IsEquivalence ∧
    (∃ c : (pointFiniteFibre D l hl E.val n hn ⋙
        (DerivedCategory.pointFiniteCohomology
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.val n))).ι).CommShift ℤ,
      ∀ T, T ∈ distTriang _ →
        (@Functor.mapTriangle _ _ _ _ _ _ _ c).obj T ∈ distTriang _) ∧
    (∃ c : (pointIntegralFibre D l hl E.val ⋙
        (DerivedCategory.pointFgComplete
          (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E.val))
          (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E.val)})).ι).CommShift ℤ,
      ∀ T, T ∈ distTriang _ →
        (@Functor.mapTriangle _ _ _ _ _ _ _ c).obj T ∈ distTriang _) ∧
    (∃ c : (pointRationalFibre D l hl E.val ⋙
        (DerivedCategory.pointFiniteDimensional E.val).ι).CommShift ℤ,
      ∀ T, T ∈ distTriang _ →
        (@Functor.mapTriangle _ _ _ _ _ _ _ c).obj T ∈ distTriang _) ∧
    (∃ c : (pointQbarFibre D l hl Ω).CommShift ℤ,
      ∀ T, T ∈ distTriang _ →
        DerivedCategory.pointFdQbarDistinguished l Ω
          ((@Functor.mapTriangle _ _ _ _ _ _ _ c).obj T))
```

## New

The identical theorem signature, verbatim:

```lean
theorem point_fibre_equivalence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (E : Padic.FiniteCoefficientFields l Ω) (n : ℕ) (hn : 1 ≤ n) :
    (pointFiniteFibre D l hl E.val n hn).IsEquivalence ∧
    (pointIntegralFibre D l hl E.val).IsEquivalence ∧
    (pointRationalFibre D l hl E.val).IsEquivalence ∧
    (pointQbarFibre D l hl Ω).IsEquivalence ∧
    (∃ c : (pointFiniteFibre D l hl E.val n hn ⋙
        (DerivedCategory.pointFiniteCohomology
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.val n))).ι).CommShift ℤ,
      ∀ T, T ∈ distTriang _ →
        (@Functor.mapTriangle _ _ _ _ _ _ _ c).obj T ∈ distTriang _) ∧
    (∃ c : (pointIntegralFibre D l hl E.val ⋙
        (DerivedCategory.pointFgComplete
          (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E.val))
          (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E.val)})).ι).CommShift ℤ,
      ∀ T, T ∈ distTriang _ →
        (@Functor.mapTriangle _ _ _ _ _ _ _ c).obj T ∈ distTriang _) ∧
    (∃ c : (pointRationalFibre D l hl E.val ⋙
        (DerivedCategory.pointFiniteDimensional E.val).ι).CommShift ℤ,
      ∀ T, T ∈ distTriang _ →
        (@Functor.mapTriangle _ _ _ _ _ _ _ c).obj T ∈ distTriang _) ∧
    (∃ c : (pointQbarFibre D l hl Ω).CommShift ℤ,
      ∀ T, T ∈ distTriang _ →
        DerivedCategory.pointFdQbarDistinguished l Ω
          ((@Functor.mapTriangle _ _ _ _ _ _ _ c).obj T))
```

Private proof helpers now construct the constant-module adjunction, descend it to derived
categories, restrict it to the prescribed subcategories, and compare the actual common-stage
fibre with a transported colimit cocone. The module adds scoped section variables and opens,
local instance registrations for these private constructions, and local irreducibility
attributes to keep the common-stage proof from unfolding large category definitions.
The elaboration options concern private proof terms only. None changes an existing public
definition or registers a new global instance in this module.

## Users

`tools/downstream.py Sheaf.Paper.PointFibreEquivalence --uses point_fibre_equivalence
pointFibreTorsionSourceTriangulated pointFibreTorsionSourceIsoClosed` reports zero downstream
modules. Each declaration occurs only in its own module. Parent DAG dependencies still
require the item, and are preserved; zero Lean importers is not used to withdraw anything.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PointFibreEquivalence | B5 | Private proof scaffolding; public interface unchanged. |

## Status

landed 20261021T110935-L-3828189 2026-10-21 (merge of deliver/B5/Sheaf.Paper.PointFibreEquivalence)
