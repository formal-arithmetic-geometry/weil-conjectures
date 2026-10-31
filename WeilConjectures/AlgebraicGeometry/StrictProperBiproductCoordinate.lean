/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantScalarTowerMates
public import WeilConjectures.AlgebraicGeometry.FiniteScalarCoordinateData
import all WeilConjectures.AlgebraicGeometry.FiniteScalarCoordinateData
import all WeilConjectures.AlgebraicGeometry.FiniteFreeScalarExtension
import all WeilConjectures.AlgebraicGeometry.CompletedAdicCoefficientDatumSupplement
import WeilConjectures.CategoryTheory.DerivedAdjunctionCochainUnit
import WeilConjectures.CategoryTheory.DerivedExactSquareCoherence

/-! Coordinate form of the strict finite proper biproduct comparison.

Source: Stacks 0B56, 0940, 0944.
(blueprint: lem-pur-compact-support-strict-scalar-mate-strict-coordinate)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Limits.limit
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

private theorem basis_mate_coordinate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [HasFiniteProducts A] [HasFiniteProducts B]
    [HasFiniteBiproducts A]
    {TW : A ⥤ C} {UW : C ⥤ A} {TZ : B ⥤ D} {UZ : D ⥤ B}
    (aW : TW ⊣ UW) (aZ : TZ ⊣ UZ)
    (RA : B ⥤ A) [RA.Additive] (RB : D ⥤ C)
    (δ : RB ⋙ UW ≅ UZ ⋙ RA)
    (d : ℕ) (κW : TW ⋙ UW ≅ finitePowerFunctor d)
    (κZ : TZ ⋙ UZ ≅ finitePowerFunctor d)
    (mW : Fin d → (UW ⟶ UW)) (mZ : Fin d → (UZ ⟶ UZ))
    (hW : ∀ (X : A) (k : Fin d),
      aW.unit.app X ≫ (mW k).app (TW.obj X) ≫ κW.hom.app X =
        Pi.lift (fun j : Fin d ↦ if k = j then 𝟙 X else 0))
    (hZ : ∀ (X : B) (k : Fin d),
      aZ.unit.app X ≫ (mZ k).app (TZ.obj X) ≫ κZ.hom.app X =
        Pi.lift (fun j : Fin d ↦ if k = j then 𝟙 X else 0))
    (hm : ∀ (M : D) (k : Fin d),
      (mW k).app (RB.obj M) ≫ δ.hom.app M =
        δ.hom.app M ≫ RA.map ((mZ k).app M))
    (N : B) (j : Fin d) :
    UW.map (((mateEquiv aZ aW).symm
        (TwoSquare.mk _ _ _ _ δ.inv)).app N) ≫
      δ.hom.app (TZ.obj N) ≫ RA.map (κZ.hom.app N) ≫
      piComparison RA (fun _ : Fin d ↦ N) ≫ Pi.π (fun _ : Fin d ↦ RA.obj N) j =
        κW.hom.app (RA.obj N) ≫ Pi.π (fun _ : Fin d ↦ RA.obj N) j := by
  classical
  dsimp only [finitePowerFunctor] at κW κZ hW hZ ⊢
  let μ := ((mateEquiv aZ aW).symm (TwoSquare.mk _ _ _ _ δ.inv)).natTrans
  have hu : aW.unit.app (RA.obj N) ≫ UW.map (μ.app N) ≫
      δ.hom.app (TZ.obj N) = RA.map (aZ.unit.app N) := by
    have h := unit_mateEquiv_symm aZ aW δ.inv N
    have h' := congrArg (fun z ↦ z ≫ δ.hom.app (TZ.obj N)) h
    simp only [Category.assoc, Iso.inv_hom_id_app] at h'
    erw [Category.comp_id] at h'
    exact h'.symm
  let P := fun _ : Fin d ↦ RA.obj N
  let q := (biproduct.isoProduct P).hom ≫ κW.inv.app (RA.obj N)
  have hq (k : Fin d) : biproduct.ι P k ≫ q =
      aW.unit.app (RA.obj N) ≫ (mW k).app (TW.obj (RA.obj N)) := by
    apply (cancel_mono (κW.hom.app (RA.obj N))).mp
    simp only [q, Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id, hW]
    apply Pi.hom_ext
    intro r
    rw [Category.assoc, biproduct.isoProduct_hom]
    change biproduct.ι P k ≫ (Pi.lift (biproduct.π P) ≫ Pi.π P r) = _
    rw [Pi.lift_π, Pi.lift_π]
    rw [biproduct.ι_π]
    split_ifs <;> rfl
  apply (cancel_epi q).mp
  apply biproduct.hom_ext'
  intro k
  simp only [← Category.assoc]
  rw [hq]
  simp only [Category.assoc]
  change aW.unit.app (RA.obj N) ≫ (mW k).app (TW.obj (RA.obj N)) ≫
      UW.map (μ.app N) ≫ δ.hom.app (TZ.obj N) ≫ RA.map (κZ.hom.app N) ≫
      piComparison RA (fun _ : Fin d ↦ N) ≫ Pi.π P j = _
  have hn := (mW k).naturality (μ.app N)
  rw [← reassoc_of% hn]
  rw [reassoc_of% hm (TZ.obj N) k]
  rw [reassoc_of% hu]
  rw [piComparison_comp_π]
  simp only [← RA.map_comp, ← Category.assoc]
  rw [Category.assoc (aZ.unit.app N), hZ,
    Category.assoc (aW.unit.app (RA.obj N)), hW, Pi.lift_π, Pi.lift_π]
  split_ifs <;> simp

private def powerColumn {A : Type*} [Category A] [Preadditive A] [HasFiniteProducts A]
    (d : ℕ) (k : Fin d) : 𝟭 A ⟶ finitePowerFunctor d where
  app X := by
    classical
    exact Pi.lift (fun j : Fin d ↦ if k = j then 𝟙 X else 0)
  naturality X Y f := by
    classical
    apply Pi.hom_ext
    intro j
    change (f ≫ Pi.lift (fun r : Fin d ↦ if k = r then 𝟙 Y else 0)) ≫
        Pi.π (fun _ : Fin d ↦ Y) j =
      (Pi.lift (fun r : Fin d ↦ if k = r then 𝟙 X else 0) ≫
        Limits.Pi.map (fun _ : Fin d ↦ f)) ≫ Pi.π (fun _ : Fin d ↦ Y) j
    simp only [Category.assoc, Pi.lift_π, Pi.map_π, Pi.lift_π_assoc]
    split_ifs <;> simp

section LocalizationHelpers
variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (F G : A ⥤ B) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

private def localizeTransformation (α : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex α (.up ℤ)) DerivedCategory.Q)

private theorem localizeTransformation_fac (α : F ⟶ G) (P : CochainComplex A ℤ) :
    (localizeTransformation F G α).app (DerivedCategory.Q.obj P) ≫
        G.mapDerivedCategoryFactors.hom.app P =
      F.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (.up ℤ)).app P) := by
  have hF : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      F.mapDerivedCategory = F.mapDerivedCategoryFactors := rfl
  have hG : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
      (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      G.mapDerivedCategory = G.mapDerivedCategoryFactors := rfl
  simp only [localizeTransformation, Localization.liftNatTrans_app, hF, hG,
    Functor.whiskerRight_app, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem factorsh_inv_cochain (P : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) =
      F.mapDerivedCategoryFactors.inv.app P := by
  have h : F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    change F.mapDerivedCategory.map (𝟙 _) ≫ _ ≫ 𝟙 _ ≫
      DerivedCategory.Qh.map (𝟙 _) = _
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
    erw [Category.comp_id, Category.comp_id]
  apply (cancel_epi (F.mapDerivedCategoryFactorsh.hom.app _)).mp
  rw [Iso.hom_inv_id_app, h, Iso.hom_inv_id_app]
  rfl

private theorem exact_unit_cochain
    [Abelian.HasKInjectiveResolutions B]
    {L : A ⥤ B} {P : B ⥤ A} [L.Additive] [P.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (a : L ⊣ P) (K : CochainComplex A ℤ) :
    (a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
      P.rightDerivedFunctorIsoMapDerivedCategory).unit.app (DerivedCategory.Q.obj K) ≫
      P.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
      P.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) := by
  have hu := derived_unit_cochain a K
  have hr := congr_app P.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((HomotopyCategory.quotient B (.up ℤ)).obj
      ((L.mapHomologicalComplex (.up ℤ)).obj K))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hr
  rw [factorsh_inv_cochain] at hr
  have hq (I : CochainComplex B ℤ) : P.rightDerivedFunctorUnitQ I =
      P.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient B (.up ℤ)).obj I) := by
    change 𝟙 _ ≫ _ ≫ P.rightDerivedFunctor.map (𝟙 _) = _
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rw [← hq] at hr
  change P.rightDerivedFunctorUnitQ _ ≫
    P.rightDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj _) = _ at hr
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc]
  rw [← reassoc_of% P.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (L.mapDerivedCategoryFactors.hom.app K)]
  rw [← Category.assoc, hu]
  simp only [Category.assoc]
  rw [← Category.assoc (P.rightDerivedFunctorUnitQ _) _ _, hr,
    Iso.inv_hom_id_app]
  erw [Category.comp_id]

private theorem localized_basis_column
    [Abelian.HasKInjectiveResolutions B]
    {L : A ⥤ B} {P : B ⥤ A} [L.Additive] [P.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (a : L ⊣ P) (d : ℕ) (c : L ⋙ P ≅ finitePowerFunctor d)
    (κ : L.mapDerivedCategory ⋙ P.mapDerivedCategory ≅ finitePowerFunctor d)
    (hκ : ∀ K : CochainComplex A ℤ,
      κ.hom.app (DerivedCategory.Q.obj K) =
        P.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
          P.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app K) ≫
          DerivedCategory.Q.map (finitePowerComplexIso d K).hom ≫
          (PreservesProduct.iso DerivedCategory.Q (fun _ : Fin d ↦ K)).hom)
    (α : P ⟶ P) (k : Fin d)
    (hc : ∀ X : A, a.unit.app X ≫ α.app (L.obj X) ≫ c.hom.app X =
      (powerColumn d k).app X)
    (X : DerivedCategory A) :
    (a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
      P.rightDerivedFunctorIsoMapDerivedCategory).unit.app X ≫
      (localizeTransformation P P α).app (L.mapDerivedCategory.obj X) ≫ κ.hom.app X =
        (powerColumn d k).app X := by
  classical
  let ad := a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    P.rightDerivedFunctorIsoMapDerivedCategory
  let αd := localizeTransformation P P α
  let lhs : 𝟭 (DerivedCategory A) ⟶ finitePowerFunctor d :=
    ad.unit ≫ Functor.whiskerLeft L.mapDerivedCategory αd ≫ κ.hom
  have he : lhs = powerColumn d k := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
    intro K
    change ad.unit.app _ ≫ αd.app _ ≫ κ.hom.app _ = _
    rw [hκ]
    rw [← reassoc_of% αd.naturality (L.mapDerivedCategoryFactors.hom.app K)]
    rw [reassoc_of% localizeTransformation_fac P P α
      ((L.mapHomologicalComplex (.up ℤ)).obj K)]
    rw [reassoc_of% exact_unit_cochain a K]
    apply Pi.hom_ext
    intro j
    simp only [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π,
      Pi.lift_π, powerColumn]
    simp only [← DerivedCategory.Q.map_comp]
    have hchain :
        (a.mapHomologicalComplex (.up ℤ)).unit.app K ≫
          (NatTrans.mapHomologicalComplex α (.up ℤ)).app
            ((L.mapHomologicalComplex (.up ℤ)).obj K) ≫
          (NatIso.mapHomologicalComplex c (.up ℤ)).hom.app K ≫
          (finitePowerComplexIso d K).hom ≫ Pi.π (fun _ : Fin d ↦ K) j =
        if k = j then 𝟙 K else 0 := by
      apply HomologicalComplex.Hom.ext
      funext n
      simp only [HomologicalComplex.comp_f]
      have hp := finitePowerComplexIso_projection d K j n
      simp only [HomologicalComplex.comp_f] at hp
      erw [hp]
      change a.unit.app (K.X n) ≫ α.app (L.obj (K.X n)) ≫
        c.hom.app (K.X n) ≫ Pi.π _ j = _
      erw [reassoc_of% hc (K.X n)]
      change Pi.lift _ ≫ Pi.π _ j = _
      rw [Pi.lift_π]
      split_ifs <;> rfl
    erw [hchain]
    split_ifs <;> simp
  exact congr_app he X

end LocalizationHelpers

universe u

private def sectionAction (W : Scheme.{u})
    (S : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (s : ∀ V : W.ProEtᵒᵖ, S.obj.obj V)
    (hs : ∀ {V V' : W.ProEtᵒᵖ} (f : V ⟶ V'), S.obj.map f (s V) = s V') :
    𝟭 (pbcModules W S) ⟶ 𝟭 (pbcModules W S) where
  app M := ⟨{
    app V := ModuleCat.ofHom {
      toFun := fun x ↦ s V • x
      map_add' := fun x y ↦ smul_add (s V) x y
      map_smul' := by
        intro r x
        exact @smul_comm (S.obj.obj V) (S.obj.obj V) (M.val.obj V)
          _ _ _ (s V) r x }
    naturality := by
      intro V V' f
      ext x
      change s V' • (show M.val.obj V' from M.val.map f x) =
        M.val.map f (s V • x)
      have h := M.val.map_smul f (s V) x
      change M.val.map f (s V • x) = S.obj.map f (s V) •
        (show M.val.obj V' from M.val.map f x) at h
      rw [hs] at h
      exact h.symm }⟩
  naturality M N f := by
    ext V x
    change s V • (f.val.app V x) = f.val.app V (s V • x)
    exact ((f.val.app V).hom.map_smul (s V) x).symm

private def basisSection (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (b : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S)))
    (k : Fin d) (V : W.ProEtᵒᵖ) : S.obj.obj V := by
  classical
  exact ((Pi.lift (fun j : Fin d ↦ if k = j then 𝟙 _ else 0) ≫ b.hom).val.app V)
    (@id (R.obj.obj V) 1)

private theorem basisSection_natural (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (b : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S)))
    (k : Fin d) {V V' : W.ProEtᵒᵖ} (f : V ⟶ V') :
    S.obj.map f (basisSection W a d b k V) = basisSection W a d b k V' := by
  classical
  have h := PresheafOfModules.naturality_apply
    (Pi.lift (fun j : Fin d ↦ if k = j then 𝟙 _ else 0) ≫ b.hom).val f (@id (R.obj.obj V) 1)
  change _ = S.obj.map f (basisSection W a d b k V) at h
  have h1 : ((SheafOfModules.unit ((adicLisseForget W).obj R)).val.map f)
      (@id (R.obj.obj V) 1) = (@id (R.obj.obj V') 1) := by
    exact (R.obj.map f).hom.map_one
  rw [h1] at h
  exact h.symm

private def basisAction (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (b : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S)))
    (k : Fin d) : 𝟭 (pbcModules W S) ⟶ 𝟭 (pbcModules W S) :=
  sectionAction W S (basisSection W a d b k) (basisSection_natural W a d b k)

private theorem basisSection_coordinate (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (b : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S)))
    (k j : Fin d) (V : W.ProEtᵒᵖ) :
    ((b.inv ≫ Pi.π (fun _ : Fin d ↦
      SheafOfModules.unit ((adicLisseForget W).obj R)) j).val.app V)
        (basisSection W a d b k V) = if k = j then (@id (R.obj.obj V) 1) else 0 := by
  classical
  have h : (Pi.lift (fun r : Fin d ↦ if k = r then 𝟙 _ else 0) ≫ b.hom) ≫
      b.inv ≫ Pi.π _ j = if k = j then 𝟙 _ else 0 := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Pi.lift_π]
  have hv := congrArg (fun f ↦ (f.val.app V) (@id (R.obj.obj V) 1)) h
  change ((b.inv ≫ Pi.π _ j).val.app V) (basisSection W a d b k V) =
    ((if k = j then 𝟙 (SheafOfModules.unit ((adicLisseForget W).obj R))
      else 0).val.app V) (@id (R.obj.obj V) 1) at hv
  rw [hv]
  split_ifs <;> rfl

private theorem ordinary_basis_column (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (b : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S)))
    (M : pbcModules W R) (k : Fin d) :
    (pbcScalarAdjunction a).unit.app M ≫
      (pbcRestrict a).map ((basisAction W a d b k).app ((pbcExtend a).obj M)) ≫
      (ordinaryCoordinates W a d b).hom.app M =
        Pi.lift (fun j : Fin d ↦ if k = j then 𝟙 M else 0) := by
  classical
  apply Pi.hom_ext
  intro j
  rw [Pi.lift_π]
  simp only [Category.assoc]
  ext V x
  have hu := (pbcScalarAdjunction_exists a).exists.choose_spec M V x
  have hc := (ordinaryCoordinates_existsUnique W a d b).exists.choose_spec
    M V (basisSection W a d b k V) x j
  have ht : pbcTensorSection a M V (basisSection W a d b k V) x =
      basisSection W a d b k V • pbcTensorSection a M V 1 x := by
    change completedAdicChangeTensor W a M V (basisSection W a d b k V) x =
      basisSection W a d b k V • completedAdicChangeTensor W a M V 1 x
    simpa only [mul_one] using
      completedTensor_smul W a M V (basisSection W a d b k V) 1 x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  dsimp only [basisAction, sectionAction, pbcRestrict, proEtaleRingRestrictScalars,
    SheafOfModules.restrictScalars, PresheafOfModules.restrictScalars,
    ModuleCat.restrictScalars, ModuleCat.RestrictScalars.map', ModuleCat.hom_ofHom]
  change ((ordinaryCoordinates W a d b).hom.app M ≫ Pi.π _ j).val.app V
      (basisSection W a d b k V • (show ((pbcExtend a).obj M).val.obj V from
        ((pbcScalarAdjunction a).unit.app M).val.app V x)) = _
  erw [hu, ← ht, hc, basisSection_coordinate]
  split_ifs <;> (simp; try rfl)


private def towerBasisAction (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (b : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S)))
    (k : Fin d) :
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a) ⟶
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).map
    (show pbcRestrict a ⟶ pbcRestrict a from
      Functor.whiskerRight (basisAction W a d b k) (pbcRestrict a))

private theorem ordinary_tower_basis_column (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (b : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S)))
    (M : pbcTowers W R) (k : Fin d) :
    ((pbcScalarAdjunction a).whiskerRight ℕᵒᵖ).unit.app M ≫
      (towerBasisAction W a d b k).app
        (((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)).obj M) ≫
      (ordinaryTowerCoordinates W a d b).hom.app M = (powerColumn d k).app M := by
  classical
  apply Pi.hom_ext
  intro j
  change _ = Pi.lift (fun r : Fin d ↦ if k = r then 𝟙 M else 0) ≫
    Pi.π (fun _ : Fin d ↦ M) j
  rw [Pi.lift_π]
  apply NatTrans.ext
  funext n
  have hp : (((ordinaryTowerCoordinates W a d b).hom.app M) ≫
      Pi.π (fun _ : Fin d ↦ M) j).app n =
      (ordinaryCoordinates W a d b).hom.app (M.obj n) ≫
        Pi.π (fun _ : Fin d ↦ M.obj n) j := by
    apply scalar_hom_ext W a d b (M.obj n) (M.obj n)
    intro V z x
    exact ((ordinaryTowerCoordinates_existsUnique W a d b).exists.choose_spec
      M (unop n) V z x j).trans
      ((ordinaryCoordinates_existsUnique W a d b).exists.choose_spec
        (M.obj n) V z x j).symm
  have h := congrArg (fun f ↦ f ≫ Pi.π (fun _ : Fin d ↦ M.obj n) j)
    (ordinary_basis_column W a d b (M.obj n) k)
  simp only [Category.assoc, Pi.lift_π] at h
  simp only [Category.assoc, NatTrans.comp_app]
  change (pbcScalarAdjunction a).unit.app (M.obj n) ≫
    (pbcRestrict a).map ((basisAction W a d b k).app ((pbcExtend a).obj (M.obj n))) ≫
      (((ordinaryTowerCoordinates W a d b).hom.app M) ≫
      Pi.π (fun _ : Fin d ↦ M) j).app n = _
  rw [hp, h]
  split_ifs <;> rfl

private theorem compatible_basis_sections
    {R S : PurCompactSupport.Coefficients.{u}} (a : PurCompactSupport.Change R S)
    {Z W : Scheme.{u}} (g : Z ⟶ W) (d : ℕ)
    (bW : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj (R.ring W))) ≅
      (pbcRestrict (a.map W)).obj
        (SheafOfModules.unit ((adicLisseForget W).obj (S.ring W))))
    (bZ : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget Z).obj (R.ring Z))) ≅
      (pbcRestrict (a.map Z)).obj
        (SheafOfModules.unit ((adicLisseForget Z).obj (S.ring Z))))
    (hb : ∀ (V : W.ProEtᵒᵖ) (s : (S.ring W).obj.obj V) (r : Fin d),
      (bZ.inv ≫ Pi.π (fun _ : Fin d ↦
        SheafOfModules.unit ((adicLisseForget Z).obj (R.ring Z))) r).val.app
          ((proEtaleBaseChange g).op.obj V)
            ((proEtaleRingDirectImageMap g (S.ring W) (S.ring Z) (S.pull g)).hom.app V s) =
      (proEtaleRingDirectImageMap g (R.ring W) (R.ring Z) (R.pull g)).hom.app V
          ((bW.inv ≫ Pi.π (fun _ : Fin d ↦
            SheafOfModules.unit ((adicLisseForget W).obj (R.ring W))) r).val.app V s))
    (V : W.ProEtᵒᵖ) (k : Fin d) :
    (proEtaleRingDirectImageMap g (S.ring W) (S.ring Z) (S.pull g)).hom.app V
      (basisSection W (a.map W) d bW k V) =
        basisSection Z (a.map Z) d bZ k ((proEtaleBaseChange g).op.obj V) := by
  classical
  let V' := (proEtaleBaseChange g).op.obj V
  let x := (proEtaleRingDirectImageMap g (S.ring W) (S.ring Z) (S.pull g)).hom.app V
    (basisSection W (a.map W) d bW k V)
  let y := basisSection Z (a.map Z) d bZ k V'
  have hxy : bZ.inv.val.app V' x = bZ.inv.val.app V' y := by
    apply SheafOfModules.sectionProduct_ext d
      (SheafOfModules.unit ((adicLisseForget Z).obj (R.ring Z))) V'
    intro j
    change (bZ.inv ≫ Pi.π _ j).val.app V' x =
      (bZ.inv ≫ Pi.π _ j).val.app V' y
    rw [hb V (basisSection W (a.map W) d bW k V) j,
      basisSection_coordinate, basisSection_coordinate]
    split_ifs
    · exact ((proEtaleRingDirectImageMap g (R.ring W) (R.ring Z)
        (R.pull g)).hom.app V).hom.map_one
    · exact ((proEtaleRingDirectImageMap g (R.ring W) (R.ring Z)
        (R.pull g)).hom.app V).hom.map_zero
  have hinv (z : (S.ring Z).obj.obj V') :
      bZ.hom.val.app V' (bZ.inv.val.app V' z) = z := by
    have h := congrArg (fun f ↦ f.val.app V' z) bZ.inv_hom_id
    exact h
  exact (hinv x).symm.trans ((congrArg (fun z ↦ bZ.hom.val.app V' z) hxy).trans (hinv y))

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)


private theorem ordinary_proper_action
    {Z W : Scheme.{u}} (g : Z ⟶ W) (d : ℕ)
    (bW : (∏ᶜ fun _ : Fin d ↦
        SheafOfModules.unit ((adicLisseForget W).obj ((constants l E).ring W))) ≅
      (pbcRestrict (constantMap l E F i W)).obj
        (SheafOfModules.unit ((adicLisseForget W).obj ((constants l F).ring W))))
    (bZ : (∏ᶜ fun _ : Fin d ↦
        SheafOfModules.unit ((adicLisseForget Z).obj ((constants l E).ring Z))) ≅
      (pbcRestrict (constantMap l E F i Z)).obj
        (SheafOfModules.unit ((adicLisseForget Z).obj ((constants l F).ring Z))))
    (hb : ∀ (V : W.ProEtᵒᵖ) (k : Fin d),
      (proEtaleRingDirectImageMap g ((constants l F).ring W) ((constants l F).ring Z)
        ((constants l F).pull g)).hom.app V
          (basisSection W (constantMap l E F i W) d bW k V) =
        basisSection Z (constantMap l E F i Z) d bZ k
          ((proEtaleBaseChange g).op.obj V))
    (M : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Z)
    (k : Fin d) :
    (towerBasisAction W (constantMap l E F i W) d bW k).app
        ((towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g).obj M) ≫
      (properRestrictionOrdinary l E F i g).hom.app M =
    (properRestrictionOrdinary l E F i g).hom.app M ≫
      (towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).map
        ((towerBasisAction Z (constantMap l E F i Z) d bZ k).app M) := by
  ext n V x
  have hd (z : (M.obj n).val.obj ((proEtaleBaseChange g).op.obj V)) :
      (((properRestrictionOrdinary l E F i g).hom.app M).app n).val.app V z = z := by
    exact congrFun (eq_of_heq
      ((properRestrictionOrdinary_existsUnique l E F i g).choose_spec.1 M (unop n) V)) z
  let V' := (proEtaleBaseChange g).op.obj V
  change (((properRestrictionOrdinary l E F i g).hom.app M).app n).val.app V
    (show (M.obj n).val.obj V' from
      (show ((constants l F).ring Z).obj.obj V' from
        (proEtaleRingDirectImageMap g ((constants l F).ring W) ((constants l F).ring Z)
          ((constants l F).pull g)).hom.app V
          (basisSection W (constantMap l E F i W) d bW k V)) •
        (show (M.obj n).val.obj V' from x)) =
    (show (M.obj n).val.obj V' from
      basisSection Z (constantMap l E F i Z) d bZ k V' •
        (show (M.obj n).val.obj V' from
          (((properRestrictionOrdinary l E F i g).hom.app M).app n).val.app V x))
  rw [hd, hd, hb]

private def derivedBasisAction (W : Scheme.{u}) (d : ℕ)
    (b : (∏ᶜ fun _ : Fin d ↦
        SheafOfModules.unit ((adicLisseForget W).obj ((constants l E).ring W))) ≅
      (pbcRestrict (constantMap l E F i W)).obj
        (SheafOfModules.unit ((adicLisseForget W).obj ((constants l F).ring W))))
    (k : Fin d) : U l E F i W ⟶ U l E F i W :=
  localizeTransformation (restrict l E F i W) (restrict l E F i W)
    (towerBasisAction W (constantMap l E F i W) d b k)

private theorem derived_basis_column (W : Scheme.{u}) (d : ℕ)
    (b : (∏ᶜ fun _ : Fin d ↦
        SheafOfModules.unit ((adicLisseForget W).obj ((constants l E).ring W))) ≅
      (pbcRestrict (constantMap l E F i W)).obj
        (SheafOfModules.unit ((adicLisseForget W).obj ((constants l F).ring W))))
    (X : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W)
    (k : Fin d) :
    (scalarAdj l E F i W).unit.app X ≫
      (derivedBasisAction l E F i W d b k).app ((T l E F i W).obj X) ≫
      (derivedTowerCoordinates W (constantMap l E F i W) d b).hom.app X =
        Pi.lift (fun j : Fin d ↦ if k = j then 𝟙 X else 0) := by
  classical
  have := (tensor_exact l E F i W).1
  have := (tensor_exact l E F i W).2
  have hκ := (derivedTowerCoordinates_normalized W
    (constantMap l E F i W) d b).choose_spec.1
  exact localized_basis_column
    ((pbcScalarAdjunction (constantMap l E F i W)).whiskerRight ℕᵒᵖ) d
    (ordinaryTowerCoordinates W (constantMap l E F i W) d b)
    (derivedTowerCoordinates W (constantMap l E F i W) d b) hκ
    (towerBasisAction W (constantMap l E F i W) d b k) k
    (fun M ↦ ordinary_tower_basis_column W (constantMap l E F i W) d b M k) X

private theorem derived_proper_basis_action {Z W : Scheme.{u}} (g : Z ⟶ W) (d : ℕ)
    (bW : (∏ᶜ fun _ : Fin d ↦
        SheafOfModules.unit ((adicLisseForget W).obj ((constants l E).ring W))) ≅
      (pbcRestrict (constantMap l E F i W)).obj
        (SheafOfModules.unit ((adicLisseForget W).obj ((constants l F).ring W))))
    (bZ : (∏ᶜ fun _ : Fin d ↦
        SheafOfModules.unit ((adicLisseForget Z).obj ((constants l E).ring Z))) ≅
      (pbcRestrict (constantMap l E F i Z)).obj
        (SheafOfModules.unit ((adicLisseForget Z).obj ((constants l F).ring Z))))
    (hb : ∀ (V : W.ProEtᵒᵖ) (s : ((constants l F).ring W).obj.obj V) (r : Fin d),
      (bZ.inv ≫ Pi.π (fun _ : Fin d ↦
        SheafOfModules.unit ((adicLisseForget Z).obj ((constants l E).ring Z))) r).val.app
          ((proEtaleBaseChange g).op.obj V)
            ((proEtaleRingDirectImageMap g ((constants l F).ring W)
              ((constants l F).ring Z) ((constants l F).pull g)).hom.app V s) =
      (proEtaleRingDirectImageMap g ((constants l E).ring W)
        ((constants l E).ring Z) ((constants l E).pull g)).hom.app V
          ((bW.inv ≫ Pi.π (fun _ : Fin d ↦
            SheafOfModules.unit ((adicLisseForget W).obj ((constants l E).ring W))) r).val.app
              V s))
    (M : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Z)
    (k : Fin d) :
    (derivedBasisAction l E F i W d bW k).app
        ((R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g).obj M) ≫
      (properRestriction l E F i g).hom.app M =
    (properRestriction l E F i g).hom.app M ≫
      (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).map
        ((derivedBasisAction l E F i Z d bZ k).app M) := by
  let PA := towerDirectImage
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g
  let PB := towerDirectImage
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g
  let αZ := towerBasisAction Z (constantMap l E F i Z) d bZ k
  let αW := towerBasisAction W (constantMap l E F i W) d bW k
  have hn : CategoryTheory.ExactDerivedSquare.unitNormalized PB PA
      (restrict l E F i Z) (restrict l E F i W)
      (U l E F i Z) (U l E F i W)
      (restrict l E F i Z).mapDerivedCategoryFactors
      (restrict l E F i W).mapDerivedCategoryFactors
      (properRestrictionOrdinary l E F i g).hom
      (properRestriction l E F i g).hom := by
    exact (properRestriction_existsUnique l E F i g).choose_spec.1
  have hs := compatible_basis_sections (change l E F i) g d bW bZ hb
  have he := CategoryTheory.ExactDerivedSquare.normalized_naturality PB PA
    (restrict l E F i Z) (restrict l E F i W)
    (restrict l E F i Z) (restrict l E F i W)
    (U l E F i Z) (U l E F i Z) (U l E F i W) (U l E F i W)
    (restrict l E F i Z).mapDerivedCategoryFactors
    (restrict l E F i Z).mapDerivedCategoryFactors
    (restrict l E F i W).mapDerivedCategoryFactors
    (restrict l E F i W).mapDerivedCategoryFactors
    (properRestrictionOrdinary l E F i g).hom
    (properRestrictionOrdinary l E F i g).hom
    (properRestriction l E F i g).hom (properRestriction l E F i g).hom hn hn
    αZ αW (derivedBasisAction l E F i Z d bZ k) (derivedBasisAction l E F i W d bW k)
    (localizeTransformation_fac _ _ αZ) (localizeTransformation_fac _ _ αW)
    (fun K ↦ ordinary_proper_action l E F i g d bW bZ hs K k)
  exact congr_app he M

/-- Each finite product projection of the strict proper scalar mate is the
corresponding projection of the normalized strict-tower coordinates.  The full
strict proper biproduct identity follows by `Pi.hom_ext`. The hypothesis `hb` says
that the source basis is transported from the target basis. This is the individual
finite-free column calculation in the whole diagram category.
Source: Stacks 0B56, equation-projection-formula-map, and 0940, section-derived-limits.
(blueprint: lem-pur-compact-support-strict-scalar-mate-strict-coordinate). -/
theorem strictProper_biproduct_coordinate {Z W : Scheme.{u}} (g : Z ⟶ W) (d : ℕ)
    (bW : (∏ᶜ fun _ : Fin d ↦
        SheafOfModules.unit ((adicLisseForget W).obj ((constants l E).ring W))) ≅
      (pbcRestrict (constantMap l E F i W)).obj
        (SheafOfModules.unit ((adicLisseForget W).obj ((constants l F).ring W))))
    (bZ : (∏ᶜ fun _ : Fin d ↦
        SheafOfModules.unit ((adicLisseForget Z).obj ((constants l E).ring Z))) ≅
      (pbcRestrict (constantMap l E F i Z)).obj
        (SheafOfModules.unit ((adicLisseForget Z).obj ((constants l F).ring Z))))
    (hb : ∀ (V : W.ProEtᵒᵖ) (s : ((constants l F).ring W).obj.obj V) (r : Fin d),
      (bZ.inv ≫ Pi.π (fun _ : Fin d ↦
        SheafOfModules.unit ((adicLisseForget Z).obj ((constants l E).ring Z))) r).val.app
          ((proEtaleBaseChange g).op.obj V)
            ((proEtaleRingDirectImageMap g ((constants l F).ring W)
              ((constants l F).ring Z) ((constants l F).pull g)).hom.app V s) =
      (proEtaleRingDirectImageMap g ((constants l E).ring W)
        ((constants l E).ring Z) ((constants l E).pull g)).hom.app V
          ((bW.inv ≫ Pi.π (fun _ : Fin d ↦
            SheafOfModules.unit ((adicLisseForget W).obj ((constants l E).ring W))) r).val.app
              V s))
    (N : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z)
    (j : Fin d) :
    (U l E F i W).map ((proper l E F i g).app N) ≫
        (properRestriction l E F i g).hom.app ((T l E F i Z).obj N) ≫
        (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).map
          ((derivedTowerCoordinates Z (constantMap l E F i Z) d bZ).hom.app N) ≫
        piComparison (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
          (fun _ : Fin d ↦ N) ≫
        Pi.π (fun _ : Fin d ↦
          (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj N) j =
      (derivedTowerCoordinates W (constantMap l E F i W) d bW).hom.app
        ((R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj N) ≫
        Pi.π (fun _ : Fin d ↦
          (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj N) j := by
  classical
  let : (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).Additive :=
    inferInstanceAs (towerDirectImage
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).rightDerivedFunctor.Additive
  apply basis_mate_coordinate (scalarAdj l E F i W) (scalarAdj l E F i Z)
    (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
    (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g)
    (properRestriction l E F i g) d
    (derivedTowerCoordinates W (constantMap l E F i W) d bW)
    (derivedTowerCoordinates Z (constantMap l E F i Z) d bZ)
    (derivedBasisAction l E F i W d bW) (derivedBasisAction l E F i Z d bZ)
  · intro X k
    exact derived_basis_column l E F i W d bW X k
  · intro X k
    exact derived_basis_column l E F i Z d bZ X k
  · intro M k
    exact derived_proper_basis_action l E F i g d bW bZ hb M k

end WeilConjectures.PurStrictScalar
