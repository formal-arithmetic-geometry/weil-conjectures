# WeilConjectures.pointUnitFiniteRestriction

## Reason

Give the existing quotient map an explicit named source and target so that restriction
and adjunction-on-complexes instance inference use the same coefficient presentation.
The wrapper is the original map itself. The new object equation is the existing
universal witness's object equation, proved by projection; it changes no object.
The finite sheaf adjunction states the same generator and cochain unit equations,
using this typed map and the named object equation. Proof irrelevance identifies the
two object-equality proofs. Explicitly naming the source of `DerivedCategory.Q` only
fixes inference. No target signature or public import changes, and no upstream module
changes. Definitions used by targets require semantic re-review: unfolding the map
wrapper gives the original construction verbatim.

## Old

```lean
abbrev pointUnitFiniteRestriction (n j : ℕ) (h : j ≤ n) :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology (Spec (.of D.k)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (pointFiniteReductionSheafMap D.k l E n j h))
```

```lean
theorem pointUnitFiniteSheafAdjunction (n j : ℕ) (h : j ≤ n) :
    ∃ a₀ : pointFiniteReductionSheafExtension D.k l E n j h ⊣
        pointUnitFiniteRestriction D l E n j h,
      (∀ (M : pointFiniteReductionSheaves D.k l E n)
        (U : (Scheme.ProEt (Spec (.of D.k)))ᵒᵖ) (x : M.val.obj U),
        (eqToHom ((pointFiniteReductionSheafExistence D.k l E n j h
          ).choose_spec.choose M)).val.app U ((a₀.unit.app M).val.app U x) =
          (toSheafify (ProEt.topology (Spec (.of D.k)))
            (SheafOfModules.changeOfRingsPresheaf
              (pointFiniteReductionSheafMap D.k l E n j h) M).presheaf).app U
                ((1 : (pointFiniteReductionRingSheaf D.k l E j).obj.obj U)
                  ⊗ₜ[(pointFiniteReductionRingSheaf D.k l E n).obj.obj U,
                    ((pointFiniteReductionSheafMap D.k l E n j h).hom.app U).hom] x)) ∧
      ∃ a : pointFiniteReductionSheafTensor D.k l E n j h ⊣
          pointUnitFiniteDerivedRestriction D l E n j h,
        ∀ P : CochainComplex (pointFiniteReductionSheaves D.k l E n) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients
            (J := ProEt.topology (Spec (.of D.k)))
            (R := pointFiniteReductionRingSheaf D.k l E n) P →
          (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
            (R := pointFiniteReductionRingSheaf D.k l E n) (P.X i)) →
          a.unit.app (DerivedCategory.Q.obj P) ≫
              (pointUnitFiniteDerivedRestriction D l E n j h).map
                (pointFiniteReductionSheafCounit D.k l E n j h P) ≫
              (pointUnitFiniteRestriction D l E n j h).mapDerivedCategoryFactors.hom.app
                ((pointFiniteReductionSheafComplexTensor D.k l E n j h).obj P) =
            DerivedCategory.Q.map ((a₀.mapHomologicalComplex (.up ℤ)).unit.app P)
```

## New

```lean
def pointUnitFiniteCoefficientMap (n j : ℕ) (h : j ≤ n) :
    pointFiniteReductionRingSheaf D.k l E n ⟶ pointFiniteReductionRingSheaf D.k l E j :=
  pointFiniteReductionSheafMap D.k l E n j h

```

```lean
theorem pointUnitFiniteExtensionObj (n j : ℕ) (h : j ≤ n)
    (M : pointFiniteReductionSheaves D.k l E n) :
    (pointFiniteReductionSheafExtension D.k l E n j h).obj M =
      SheafOfModules.changeOfRings (pointUnitFiniteCoefficientMap D l E n j h) M := by
  exact (pointFiniteReductionSheafExistence D.k l E n j h).choose_spec.choose M
```

```lean
abbrev pointUnitFiniteRestriction (n j : ℕ) (h : j ≤ n) :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology (Spec (.of D.k)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (pointUnitFiniteCoefficientMap D l E n j h))
```

```lean
theorem pointUnitFiniteSheafAdjunction (n j : ℕ) (h : j ≤ n) :
    ∃ a₀ : pointFiniteReductionSheafExtension D.k l E n j h ⊣
        pointUnitFiniteRestriction D l E n j h,
      (∀ (M : pointFiniteReductionSheaves D.k l E n)
        (U : (Scheme.ProEt (Spec (.of D.k)))ᵒᵖ) (x : M.val.obj U),
        (eqToHom (pointUnitFiniteExtensionObj D l E n j h M)).val.app U
            ((a₀.unit.app M).val.app U x) =
          (toSheafify (ProEt.topology (Spec (.of D.k)))
            (SheafOfModules.changeOfRingsPresheaf
              (pointUnitFiniteCoefficientMap D l E n j h) M).presheaf).app U
                ((1 : (pointFiniteReductionRingSheaf D.k l E j).obj.obj U)
                  ⊗ₜ[(pointFiniteReductionRingSheaf D.k l E n).obj.obj U,
                    ((pointUnitFiniteCoefficientMap D l E n j h).hom.app U).hom] x)) ∧
      ∃ a : pointFiniteReductionSheafTensor D.k l E n j h ⊣
          pointUnitFiniteDerivedRestriction D l E n j h,
        ∀ P : CochainComplex (pointFiniteReductionSheaves D.k l E n) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients
            (J := ProEt.topology (Spec (.of D.k)))
            (R := pointFiniteReductionRingSheaf D.k l E n) P →
          (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
            (R := pointFiniteReductionRingSheaf D.k l E n) (P.X i)) →
          a.unit.app (DerivedCategory.Q.obj P) ≫
              (pointUnitFiniteDerivedRestriction D l E n j h).map
                (pointFiniteReductionSheafCounit D.k l E n j h P) ≫
              (pointUnitFiniteRestriction D l E n j h).mapDerivedCategoryFactors.hom.app
                ((pointFiniteReductionSheafComplexTensor D.k l E n j h).obj P) =
            (DerivedCategory.Q (C := pointFiniteReductionSheaves D.k l E n)).map
              ((a₀.mapHomologicalComplex (.up ℤ)).unit.app P)
```

The two restriction exactness proofs use the typed map. The sections restriction
proof uses it as well. These are proof changes with the same conclusions.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PointReductionUnits | A9 | Typed coefficient interface and the same normalized units. |
| Sheaf.Paper.PointReductionUnitNormalization | unclaimed | Same unit and comparison constructions; no adaptation. |

## Status

landed 20261021T002923-L-1578406 2026-10-21 (merge of deliver/A9/Sheaf.Paper.PointReductionUnits)
