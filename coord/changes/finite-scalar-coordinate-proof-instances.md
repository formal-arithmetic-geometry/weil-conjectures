# WeilConjectures.PurStrictScalar.finiteScalarTower

## Reason

The five normalized coordinate proofs exposed expensive unfolding of the chosen tower
functor and the uniqueness predicates of coordinate choices. Local irreducibility boundaries, respecting transparency for the final tower declarations,
and explicit return types keep these constructions from being expanded during later checks.
Each coordinate definition now chooses from the existence part of the same uniqueness theorem.
Both choices satisfy exactly the same normalization, so uniqueness proves their equality;
no downstream mathematical statement changes. The exact-localization functor and counit retain
their constructions, with `haveI` instance bindings written as `have`. The restriction colimit
instance explicitly supplies already available sheafification instances. No public imports,
visibility, or elaborated declaration types change.

The repair also names the existing finite-product instance of ordinary strict
towers as `scalarTower_products`, parallel to `scalarTowerDerived_products`.
This caches the pointwise product proof before the repeated coordinate types are
elaborated. The full module with this cache compiled in 36.3 seconds. The instance
is proved by `inferInstance`; it adds no assumptions and changes no existing type.

## Old

```lean
instance scalarTowerRestriction_colimits (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a)) :=
  ⟨fun _ _ _ ↦ inferInstance⟩
```

```lean
def finiteScalarTower (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    DerivedCategory (pbcTowers W R) ⥤ DerivedCategory (pbcTowers W S) :=
  haveI := (finiteScalar_exact W a d e).1
  haveI := (finiteScalar_exact W a d e).2
  haveI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  haveI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)).mapDerivedCategory
```

```lean
def finiteScalarTowerCounit (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S)))
    (P : CochainComplex (pbcTowers W R) ℤ) :
    (finiteScalarTower W a d e).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)).mapHomologicalComplex
          (.up ℤ)).obj P) :=
  haveI := (finiteScalar_exact W a d e).1
  haveI := (finiteScalar_exact W a d e).2
  haveI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  haveI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)).mapDerivedCategoryFactors.hom.app P
```

```lean
def ordinaryCoordinates (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :=
  (ordinaryCoordinates_existsUnique W a d e).choose
```

```lean
def derivedCoordinates (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :=
  (derivedCoordinates_existsUnique W a d e).choose
```

```lean
def ordinaryTowerCoordinates (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :=
  (ordinaryTowerCoordinates_existsUnique W a d e).choose
```

```lean
def derivedTowerCoordinates (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :=
  (derivedTowerCoordinates_existsUnique W a d e).choose
```

## New

```lean
instance scalarTower_products (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) :
    HasFiniteProducts (pbcTowers W R) := inferInstance
```

```lean
def ordinaryCoordinates (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    pbcExtend a ⋙ pbcRestrict a ≅ finitePowerFunctor d :=
  (ordinaryCoordinates_existsUnique W a d e).exists.choose
```

```lean
def derivedCoordinates (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    pbcDerivedExtend a ⋙ pbcDerivedRestrict a ≅ finitePowerFunctor d :=
  (derivedCoordinates_existsUnique W a d e).exists.choose
```

```lean
def ordinaryTowerCoordinates (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a) ⋙
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a) ≅ finitePowerFunctor d :=
  (ordinaryTowerCoordinates_existsUnique W a d e).exists.choose
```

```lean
instance scalarTowerRestriction_colimits (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a)) := by
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} := inferInstance
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance
  exact ⟨fun _ _ _ ↦ inferInstance⟩
```

```lean
instance scalarTowerDerived_products (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) :
    HasFiniteProducts (DerivedCategory (pbcTowers W R)) := inferInstance
```

```lean
instance scalarTowerExtension_additive (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) :
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)).Additive := inferInstance
```

```lean
instance scalarTowerRestriction_additive (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) :
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a)).Additive := inferInstance
```

```lean
theorem scalarTowerExtension_exact (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)) ∧
      PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)) := by
  have := (finiteScalar_exact W a d e).1
  have := (finiteScalar_exact W a d e).2
  exact ⟨⟨fun _ _ _ ↦ inferInstance⟩, ⟨fun _ _ _ ↦ inferInstance⟩⟩
```

```lean
def finiteScalarTower (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    DerivedCategory (pbcTowers W R) ⥤ DerivedCategory (pbcTowers W S) :=
  have := (scalarTowerExtension_exact W a d e).1
  have := (scalarTowerExtension_exact W a d e).2
  ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)).mapDerivedCategory
```

```lean
def finiteScalarTowerCounit (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S)))
    (P : CochainComplex (pbcTowers W R) ℤ) :
    (finiteScalarTower W a d e).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)).mapHomologicalComplex
          (.up ℤ)).obj P) :=
  have := (scalarTowerExtension_exact W a d e).1
  have := (scalarTowerExtension_exact W a d e).2
  ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)).mapDerivedCategoryFactors.hom.app P
```

```lean
def derivedTowerCoordinateNormalization (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S)))
    (κ : finiteScalarTower W a d e ⋙
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a)).mapDerivedCategory ≅
          finitePowerFunctor d) : Prop :=
    ∀ P : CochainComplex (pbcTowers W R) ℤ,
      κ.hom.app (DerivedCategory.Q.obj P) =
        (((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a)).mapDerivedCategory).map
            (finiteScalarTowerCounit W a d e P) ≫
          ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            (pbcRestrict a)).mapDerivedCategoryFactors.hom.app
            ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)).mapHomologicalComplex
              (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (ordinaryTowerCoordinates W a d e) (.up ℤ)).hom.app P) ≫
          DerivedCategory.Q.map (finitePowerComplexIso d P).hom ≫
          (PreservesProduct.iso DerivedCategory.Q (fun _ : Fin d ↦ P)).hom
```

```lean
theorem derivedTowerCoordinates_normalized (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    ∃! κ : finiteScalarTower W a d e ⋙
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a)).mapDerivedCategory ≅
          finitePowerFunctor d,
      derivedTowerCoordinateNormalization W a d e κ := by
  exact derivedTowerCoordinates_existsUnique W a d e
```

```lean
def derivedTowerCoordinates (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    finiteScalarTower W a d e ⋙
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a)).mapDerivedCategory ≅
        finitePowerFunctor d :=
  (derivedTowerCoordinates_normalized W a d e).choose
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FiniteScalarCoordinateData | J7 | Own proofs; same constructions and proposition instances. |
| Sheaf.Paper.CompactSupportStrictScalarMate | unclaimed | Same coordinate isomorphism type; no adaptation needed. |
| Sheaf.Paper.CompactSupportScalarLimitReduction | unclaimed | Same coordinate isomorphism type; no adaptation needed. |
| Sheaf.Paper.CompactSupportScalarShiftNormalization | unclaimed | Same coordinate isomorphism type; no adaptation needed. |
| Sheaf.Paper.CompactSupportStrictScalarComposition | unclaimed | Same coordinate isomorphism type; no adaptation needed. |
| Sheaf.Paper.CompactSupportStrictScalarRefinement | unclaimed | Same coordinate isomorphism type; no adaptation needed. |

All users reported by downstream.py, including indirect users, are listed. No target
meaning changes and no consumer adaptations are required.

## Status

landed 20261025T003325-L-3229127 2026-10-25 (merge of deliver/J7/Sheaf.Paper.FiniteScalarCoordinateData)
