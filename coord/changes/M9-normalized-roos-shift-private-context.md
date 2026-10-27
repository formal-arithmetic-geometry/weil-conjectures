# CategoryTheory.normalizedRoosShiftComparison: private proof context

## Reason

The item is proved from the existing signed localization and derived-limit unit
computation. The proof needs private helpers for the ordinary-limit identification,
unit transfer, and generic categorical assembly. Section variables support those
private declarations. The static interface scanner flags the section-variable and
option commands, so this record documents them explicitly. The public theorem
signature and both public imports are verbatim. All new declarations are private;
there are no new public instances, notation, or attributes.

The private `assembledAbelian` instance packages the existing preadditive structure
and abelian properties, making its preadditive projection immediate. It is local
to `FastAbelian` and introduces no public category structure. The final theorem
scopes `backward.isDefEq.respectTransparency.types true` to avoid unnecessary
unfolding during type elaboration. No source-library declaration is modified.

The returned duplicate projection wrapper is removed. The naturality proof now
uses Mathlib's `IsLimit.conePointUniqueUpToIso_hom_comp` directly, after unfolding
the private point isomorphism. The matching library wrappers are private, so
importing their modules cannot expose them. No replacement statement is added.

## Old

The original context preceding the sole theorem was:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC t w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

```

## New

The corresponding context, including the proved private helpers, is:

```lean
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe uC vC t w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

section

variable {A : Type*} [Category* A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]

private noncomputable def limitModelCone (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    Cone I.asFunctor where
  pt := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) |>.obj I
  π :=
    { app := fun n ↦ (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app I
      naturality := by
        intro n m f
        ext q
        change 𝟙 (limit (I.X q)) ≫ limit.π (I.X q) m =
          limit.π (I.X q) n ≫ (I.X q).map f
        rw [Category.id_comp, limit.w] }

private noncomputable def limitModelLimit (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    IsLimit (limitModelCone I) := by
  apply HomologicalComplex.isLimitOfEval
  intro q
  exact limit.isLimit (I.X q)

private noncomputable def limitModelPointIso (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I ≅
      limit I.asFunctor :=
  (limitModelLimit I).conePointUniqueUpToIso (limit.isLimit I.asFunctor)

private noncomputable def limitModelIso :
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ≅
      roosLimitFunctor :=
  NatIso.ofComponents limitModelPointIso (by
    intro X Y f
    change (lim.mapHomologicalComplex (.up ℤ)).map f ≫ (limitModelPointIso Y).hom =
      (limitModelPointIso X).hom ≫ lim.map
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f)
    apply limit.hom_ext
    intro n
    dsimp only [limitModelPointIso]
    erw [Category.assoc,
      IsLimit.conePointUniqueUpToIso_hom_comp (limitModelLimit Y)
        (limit.isLimit Y.asFunctor) n, lim_map, Category.assoc, limMap_π]
    erw [← Category.assoc,
      IsLimit.conePointUniqueUpToIso_hom_comp (limitModelLimit X)
        (limit.isLimit X.asFunctor) n]
    exact (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).naturality f)

end

private theorem derivedLimitUnitIso
    {A : Type uC} [Category.{vC} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    (L RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η₀ : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ L)
    (η : roosLimitFunctor (A := A) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RF)
    (hL : L.IsRightDerivedFunctor η₀
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)))
    (_hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)))
    (hη₀ : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ), I.IsKInjective → IsIso (η₀.app I))
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] : IsIso (η.app I) := by
  classical
  let QT := DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ A)
  let QA := DerivedCategory.Q.{w} (C := A)
  let := hL
  let := _hRF
  let e := Functor.isoWhiskerRight (limitModelIso (A := A)) QA
  let δ := L.rightDerivedNatIso RF (L := QT) η₀ η
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) e
  have he := L.rightDerivedNatTrans_app RF (L := QT) η₀ η
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) e.hom I
  have := hη₀ I inferInstance
  have heq : η.app I = e.inv.app I ≫ η₀.app I ≫ δ.hom.app (QT.obj I) := by
    have he' := congrArg (fun z ↦ e.inv.app I ≫ z) he
    simpa only [δ, Functor.rightDerivedNatIso_hom, Iso.inv_hom_id_app_assoc] using he'.symm
  exact heq.symm ▸ (inferInstance : IsIso
    (e.inv.app I ≫ η₀.app I ≫ δ.hom.app (QT.obj I)))

section FastAbelian

variable {A : Type uC} [Category.{vC} A] [Preadditive A]
  [IsNormalMonoCategory A] [IsNormalEpiCategory A]
  [HasFiniteProducts A] [HasKernels A] [HasCokernels A]

private local instance assembledAbelian : Abelian A where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := inferInstance
  toIsNormalEpiCategory := inferInstance
  has_finite_products := inferInstance
  has_kernels := inferInstance
  has_cokernels := inferInstance

private theorem normalizedRoosShiftAssembly
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    (RF CF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤
      DerivedCategory.{w} (A))
    (η : roosLimitFunctor (A := A) ⋙
      DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF)
    (_hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)))
    (hηiso : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective], IsIso (η.app I))
    (κ : roosF (A := A) ⋙
      DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ CF)
    (ρ : CF ≅ RF)
    (_hnorm : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      DerivedCategory.Q.{w}.map (roosι X) ≫ κ.hom.app X ≫
        ρ.hom.app (DerivedCategory.Q.{w}.obj X) = η.app X) :
    ∃ (cC : (roosF (A := A)).CommShift ℤ)
      (cD : CF.CommShift ℤ) (cR : RF.CommShift ℤ)
      (cL : (roosLimitFunctor (A := A)).CommShift ℤ),
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
        (r q : ℤ) (n : ℕ),
        (((Functor.commShiftIso roosF (self := cC) r).hom.app X).f q ≫
            (CochainComplex.shiftFunctorObjXIso (roosF.obj X) r q (q + r) rfl).hom ≫
            (roosProj X).f (q + r) ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (q + r) =
          (roosProj (X⟦r⟧)).f q ≫
            (Pi.π (fun k : ℕ ↦ (X⟦r⟧).asFunctor.obj (op k)) n).f q ≫
            ((CochainComplex.shiftFunctorObjXIso X r q (q + r) rfl).hom).app (op n)) ∧
        (((Functor.commShiftIso roosF (self := cC) r).hom.app X).f q ≫
            (CochainComplex.shiftFunctorObjXIso (roosF.obj X) r q (q + r) rfl).hom ≫
            (CochainComplex.mappingCocone.snd (roosU X)).v
              (q + r) ((q - 1) + r) (by omega) ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f ((q - 1) + r) =
          r.negOnePow • ((CochainComplex.mappingCocone.snd (roosU (X⟦r⟧))).v
              q (q - 1) (by omega) ≫
            (Pi.π (fun k : ℕ ↦ (X⟦r⟧).asFunctor.obj (op k)) n).f (q - 1) ≫
            ((CochainComplex.shiftFunctorObjXIso X r (q - 1) ((q - 1) + r) rfl).hom).app
              (op n)))) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ),
        DerivedCategory.Q.{w}.map ((Functor.commShiftIso roosF (self := cC) r).hom.app X) ≫
            (DerivedCategory.Q.{w}.commShiftIso r).hom.app (roosF.obj X) ≫
            (κ.hom.app X)⟦r⟧' =
          κ.hom.app (X⟦r⟧) ≫ CF.map ((DerivedCategory.Q.{w}.commShiftIso r).hom.app X) ≫
            (Functor.commShiftIso CF (self := cD) r).hom.app (DerivedCategory.Q.{w}.obj X)) ∧
      (∀ (N : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) (r : ℤ),
        ρ.hom.app (N⟦r⟧) ≫ (Functor.commShiftIso RF (self := cR) r).hom.app N =
          (Functor.commShiftIso CF (self := cD) r).hom.app N ≫ (ρ.hom.app N)⟦r⟧') ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
        (r q : ℤ) (n : ℕ),
        ((Functor.commShiftIso roosLimitFunctor (self := cL) r).hom.app I).f q ≫
            (CochainComplex.shiftFunctorObjXIso (limit I.asFunctor) r q (q + r) rfl).hom ≫
            (limit.π I.asFunctor (op n)).f (q + r) =
          (limit.π (I⟦r⟧).asFunctor (op n)).f q ≫
            ((CochainComplex.shiftFunctorObjXIso I r q (q + r) rfl).hom).app (op n)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
        [I.IsKInjective] (r : ℤ),
        roosι (I⟦r⟧) ≫ (Functor.commShiftIso roosF (self := cC) r).hom.app I =
          (Functor.commShiftIso roosLimitFunctor (self := cL) r).hom.app I ≫ (roosι I)⟦r⟧') ∧
      (∀ (X I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
        (q : X ⟶ I) [QuasiIso q] [I.IsKInjective] (r : ℤ),
        ∃ (d : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅
            RF.obj (DerivedCategory.Q.{w}.obj X))
          (ds : DerivedCategory.Q.{w}.obj (limit (I⟦r⟧).asFunctor) ≅
            RF.obj (DerivedCategory.Q.{w}.obj (X⟦r⟧))),
          d.hom ≫ RF.map (DerivedCategory.Q.{w}.map q) = η.app I ∧
          ds.hom ≫ RF.map (DerivedCategory.Q.{w}.map (q⟦r⟧')) = η.app (I⟦r⟧) ∧
          ds.hom ≫ RF.map ((DerivedCategory.Q.{w}.commShiftIso r).hom.app X) ≫
              (Functor.commShiftIso RF (self := cR) r).hom.app (DerivedCategory.Q.{w}.obj X) =
            DerivedCategory.Q.{w}.map
                ((Functor.commShiftIso roosLimitFunctor (self := cL) r).hom.app I) ≫
              (DerivedCategory.Q.{w}.commShiftIso r).hom.app (limit I.asFunctor) ≫ d.hom⟦r⟧') := by
  classical
  let QT := DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ A)
  let QA := DerivedCategory.Q.{w} (C := A)
  have h := strictRoosShiftLocalization (A := A) QT QA CF κ
  rcases h with ⟨cC, cL, hcoord, _, hlim, hinc, cD, ⟨hdesc, hloc⟩, _⟩
  let := cD
  let cR := Functor.CommShift.ofIso ρ ℤ
  have hsquare (N : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) (r : ℤ) :
      ρ.hom.app (N⟦r⟧) ≫ (Functor.commShiftIso RF (self := cR) r).hom.app N =
        (Functor.commShiftIso CF (self := cD) r).hom.app N ≫ (ρ.hom.app N)⟦r⟧' := by
    simp [cR, Functor.CommShift.ofIso_commShiftIso_hom_app]
  have hηshift (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ) :
      η.app (I⟦r⟧) ≫ RF.map ((QT.commShiftIso r).hom.app I) ≫
          (Functor.commShiftIso RF (self := cR) r).hom.app (QT.obj I) =
        QA.map ((Functor.commShiftIso roosLimitFunctor (self := cL) r).hom.app I) ≫
          (QA.commShiftIso r).hom.app (limit I.asFunctor) ≫ (η.app I)⟦r⟧' := by
    let u := (QT.commShiftIso r).hom.app I
    let v := (Functor.commShiftIso RF (self := cR) r).hom.app (QT.obj I)
    have hn : ρ.hom.app (QT.obj (I⟦r⟧)) ≫ RF.map u =
        CF.map u ≫ ρ.hom.app ((QT.obj I)⟦r⟧) :=
      (ρ.hom.naturality u).symm
    have hn' := congrArg (fun z ↦ z ≫ v) hn
    have hs := congrArg (fun z ↦ CF.map u ≫ z) (hsquare (QT.obj I) r)
    have hc : ρ.hom.app (QT.obj (I⟦r⟧)) ≫ RF.map u ≫ v =
        CF.map u ≫ (Functor.commShiftIso CF (self := cD) r).hom.app (QT.obj I) ≫
          (ρ.hom.app (QT.obj I))⟦r⟧' := by
      exact (Category.assoc _ _ _).symm.trans
        (hn'.trans ((Category.assoc _ _ _).trans hs))
    have hh := congrArg (fun z ↦ QA.map (roosι (I⟦r⟧)) ≫ κ.hom.app (I⟦r⟧) ≫ z) hc
    have hl := congrArg (fun z ↦ z ≫ (ρ.hom.app (QT.obj I))⟦r⟧') (hloc I r)
    simp only [Functor.map_comp, Category.assoc] at hh hl
    have hleft := congrArg (fun z ↦ z ≫ RF.map u ≫ v) (_hnorm (I⟦r⟧))
    have hright := congrArg (fun z ↦
      QA.map ((Functor.commShiftIso roosLimitFunctor (self := cL) r).hom.app I) ≫
        (QA.commShiftIso r).hom.app (limit I.asFunctor) ≫ z⟦r⟧') (_hnorm I)
    simp only [Functor.map_comp, Category.assoc] at hleft hright
    dsimp only [QT, QA, roosLimitFunctor, Functor.comp_obj,
      HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj] at hleft hh hl hright ⊢
    set_option backward.isDefEq.respectTransparency false in
      simp only [Category.assoc] at hl
    set_option backward.isDefEq.respectTransparency true in
      exact hleft.symm.trans (hh.trans (hl.trans hright))
  dsimp only [QT, QA] at hcoord hdesc hsquare hlim hinc hηshift hηiso
  refine ⟨cC, cD, cR, cL, ?_⟩
  refine And.intro ?_ ?_
  · intro X r q n
    with_reducible exact hcoord X r q n
  refine And.intro ?_ ?_
  · intro X r
    with_reducible exact hdesc X r
  refine And.intro ?_ ?_
  · intro N r
    with_reducible exact hsquare N r
  refine And.intro ?_ ?_
  · intro I r q n
    set_option backward.isDefEq.respectTransparency true in
      with_reducible exact hlim I r q n
  constructor
  · intro I _ r
    set_option backward.isDefEq.respectTransparency true in
      with_reducible exact hinc I r
  · intro X I q _ _ r
    have := hηiso I
    have := hηiso (I⟦r⟧)
    let d₀ := asIso (η.app I)
    let ds₀ := asIso (η.app (I⟦r⟧))
    dsimp only [roosLimitFunctor, Functor.comp_obj,
      HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj] at d₀ ds₀
    let d := d₀ ≪≫ (RF.mapIso (asIso (QT.map q))).symm
    let ds := ds₀ ≪≫
      (RF.mapIso (asIso (QT.map (q⟦r⟧')))).symm
    have hd : d.hom ≫ RF.map (QT.map q) = η.app I := by simp [d, d₀]
    have hds : ds.hom ≫ RF.map (QT.map (q⟦r⟧')) = η.app (I⟦r⟧) := by simp [ds, ds₀]
    refine ⟨d, ds, hd, hds, ?_⟩
    apply (cancel_mono ((RF.map (QT.map q))⟦r⟧')).1
    have hn := (Functor.commShiftIso RF (self := cR) r).hom.naturality (QT.map q)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    have hq := (QT.commShiftIso r).hom.naturality q
    dsimp only [Functor.comp_map, Functor.comp_obj] at hq
    have ht := congrArg RF.map hq
    simp only [Functor.map_comp] at ht
    have e₁ := congrArg (fun z ↦ ds.hom ≫
      RF.map ((QT.commShiftIso r).hom.app X) ≫ z) hn.symm
    have e₂ := congrArg (fun z ↦ ds.hom ≫ z ≫
      (Functor.commShiftIso RF (self := cR) r).hom.app (QT.obj I)) ht.symm
    have e₃ := congrArg (fun z ↦ z ≫ RF.map ((QT.commShiftIso r).hom.app I) ≫
      (Functor.commShiftIso RF (self := cR) r).hom.app (QT.obj I)) hds
    dsimp only [QT, QA, roosLimitFunctor, Functor.comp_obj,
      HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj] at hd hds hηshift ⊢
    have e₄ := congrArg (fun z ↦
      QA.map ((Functor.commShiftIso roosLimitFunctor (self := cL) r).hom.app I) ≫
        (QA.commShiftIso r).hom.app (limit I.asFunctor) ≫ z⟦r⟧') hd
    simp only [Functor.map_comp, Category.assoc] at e₁ e₂ e₃ e₄
    dsimp only [QT, QA, roosLimitFunctor, Functor.comp_obj,
      HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj] at e₄ hηshift ⊢
    simp only [Category.assoc]
    exact e₁.trans (e₂.trans (e₃.trans ((hηshift I r).trans e₄.symm)))

end FastAbelian

set_option backward.isDefEq.respectTransparency.types true in
```

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.NormalizedRoosShiftComparison
--uses normalizedRoosShiftComparison` reports the following sole downstream module.
Its source imports the item for proofs and does not mention the theorem by name.
The claim record for the consumer is absent at this check.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.NormalizedRoosShiftComparison | M9 | One theorem hole closed; private proof context added. |
| Sheaf.Paper.IntegralImmersionPullbackNormalization | unclaimed | Existing theorem signature and public imports preserved; no adaptation. |

## Status

landed 20261024T190354-L-4036779 2026-10-24 (merge of deliver/M9/Sheaf.CategoryTheory.NormalizedRoosShiftComparison)
