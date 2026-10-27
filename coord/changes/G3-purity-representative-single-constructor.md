# puritySingleFromRepresentativeMap and purityRepresentativeSingleMap

## Reason

Expose the original scalar/single representative construction in abstract categories, with both
adjunctions and their endpoints shared before coefficient-site specialization. The adjunction
comparison can then be proved once without expanding the site-specific derived functors.
The scalar/single definition keeps its original adjunction formula. The proved generic theorem
`CategoryTheory.purityAdjunctionSingleMap_eq_representative` identifies it with the original
adjunction transpose; signatures and mathematical maps are unchanged.

## Old

The generic declarations did not exist. The original four-factor scalarSingleMap formula
is recovered by the published `scalarSingleMap_cochain` (T8). The original purity scalar map was:

```lean
/-- The comparison on a sheaf in degree zero is the scalar transpose of the ordinary
scalar-unit map, followed by the exact restriction/single comparison.
Source: Stacks 06YY (blueprint: def-pur-vector-purity-scalar-single). -/
def purityScalarSingleMap {A A' : Type (u + 1)} [CommRing A] [CommRing A']
    (φ : A →+* A') (T : Scheme.{u})
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (Etale.purityScalarExtension φ T).obj ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (DerivedCategory.singleFunctor _ 0).obj ((Etale.purityScalarSheaf φ T).obj M) :=
  purityAdjunctionSingleMap (Etale.purityScalarSheaf φ T)
    (Sheaf.restrictScalars T.smallEtaleTopology φ) (Etale.purityScalarExtension φ T)
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)
    (DerivedCategory.singleFunctor _ 0) (DerivedCategory.singleFunctor _ 0)
    (Etale.purityScalarSheafAdjunction φ T) (Etale.purityScalarAdjunction φ T)
    ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor 0) M
```

## New

```lean
/-- Form a single-object comparison from a cochain representative transformation.
The single/quotient comparisons on both sides are the existing canonical ones.
Source: Stacks 06YY (blueprint: def-pur-vector-purity-scalar-single). -/
def puritySingleFromRepresentativeMap
    {C : Type v₁} {D : Type v₂} [Category.{w₁} C] [Category.{w₂} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w₃} C] [HasDerivedCategory.{w₄} D]
    (F : C ⥤ D) [F.Additive] (E : DerivedCategory C ⥤ DerivedCategory D)
    (rep : ∀ P : CochainComplex C ℤ, E.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) (M : C) :
    E.obj ((DerivedCategory.singleFunctor C 0).obj M) ⟶
      (DerivedCategory.singleFunctor D 0).obj (F.obj M) :=
  E.map ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app M) ≫
    rep ((CochainComplex.singleFunctor C 0).obj M) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M) ≫
    (DerivedCategory.singleFunctorIsoCompQ D 0).inv.app (F.obj M)

section RepresentativeSingle

variable {C : Type v₁} {D : Type v₂} [Category.{w₁} C] [Category.{w₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{w₃} C] [HasDerivedCategory.{w₄} D]
  (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (adj : E ⊣ U) (L : DerivedCategory C ⥤ DerivedCategory D)
  (ad : L ⊣ U.mapDerivedCategory)

/-- The representative scalar/single arrow, sharing its ordinary and derived adjunctions.
This is the localized cochain-unit formula, with the single/quotient comparisons on both sides.
Source: Stacks 06YY and 07A6 (blueprint: def-pur-vector-purity-scalar-single). -/
def purityRepresentativeSingleMap (M : C) :
    L.obj ((DerivedCategory.singleFunctor C 0).obj M) ⟶
      (DerivedCategory.singleFunctor D 0).obj (E.obj M) :=
    puritySingleFromRepresentativeMap E L
    (Etale.scalarAdjunctionRepresentativeMap E U adj L ad) M

end RepresentativeSingle
```

The public generic equality theorem proves that this formula is exactly the original
adjunction transpose. Its proof cancels the exact-restriction quotient comparison,
uses naturality, and checks the single complex in degree zero; other degrees are zero.

```lean
/-- The adjunction and representative single comparisons agree.
Source: Stacks 06YY, 07A6 (blueprint: def-pur-vector-purity-scalar-single). -/
theorem purityAdjunctionSingleMap_eq_representative (M : C) :
    WeilConjectures.PurityFiniteSetting.purityAdjunctionSingleMap E U L U.mapDerivedCategory
      (DerivedCategory.singleFunctor C 0) (DerivedCategory.singleFunctor D 0)
      adj ad (U.mapDerivedCategorySingleFunctor 0) M =
    WeilConjectures.PurityFiniteSetting.purityRepresentativeSingleMap E U adj L ad M := by
  unfold WeilConjectures.PurityFiniteSetting.purityRepresentativeSingleMap
    WeilConjectures.PurityFiniteSetting.puritySingleFromRepresentativeMap
    Etale.scalarAdjunctionRepresentativeMap
  rw [← AlgebraicGeometry.Etale.mapComplex_unit_formula]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app]
  erw [L.map_id, Category.id_comp, Category.comp_id]
  exact single_adjunction_formula E U adj L ad M
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | Adds generic constructions and a proved comparison API; original scalar/single definition. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Not changed (reviewer fix 2026-10-26: published module kept, `scalarSingleMap := purityScalarSingleMap` as landed by T8). |
| Sheaf.Paper.FiniteTateScalarSourceNormalization | G3 | Uses the shared representative formula and its invertibility. |

All previous consumers retain the same signatures and public imports. The generic theorem identifies the two formulas. No target changes.

| Sheaf.Paper.OrderedTateScalarNormalization | unclaimed | Same scalar/single arrow. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | Same scalar/single arrow. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Same scalar/single arrow. |
| Sheaf.SixFunctors.AffineDualizingCoefficient | unclaimed | Same scalar/single arrow. |

## Status

landed 20261025T202103-L-2672233 2026-10-25 (merge of deliver/G3/Sheaf.Paper.FiniteTateScalarSourceNormalization)
