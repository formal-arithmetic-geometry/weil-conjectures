/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.SecSmoothPurity.DirectImageScalarExchange
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-! # Coefficient associativity for canonical scalar comparisons

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-direct-image.proof.md (blueprint: lem-sp-pullback-scalar-coefficient-cocycle).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem balance_unit
    (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c)
    (P : CochainComplex (proEtaleRingModules T R) ℤ) :
    (NatTrans.mapHomologicalComplex (pbcScalarAdjunction a).unit (.up ℤ)).app P ≫
      ((pbcRestrict a).mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction b).unit (.up ℤ)).app
          ((reductionChangeComplex T a).obj P)) ≫
      (NatTrans.mapHomologicalComplex (pbcRestrictComp a b c h).hom (.up ℤ)).app
        ((reductionChangeComplex T b).obj ((reductionChangeComplex T a).obj P)) ≫
      ((pbcRestrict c).mapHomologicalComplex (.up ℤ)).map
        (reductionBalance T a b c h P) =
      (NatTrans.mapHomologicalComplex (pbcScalarAdjunction c).unit (.up ℤ)).app P := by
  ext i U x
  change (P.X i).val.obj U at x
  change ((reductionBalance T a b c h P).f i).val.app U
    (((pbcRestrictComp a b c h).hom.app _).val.app U
      (((pbcScalarAdjunction b).unit.app _).val.app U
        (((pbcScalarAdjunction a).unit.app (P.X i)).val.app U x))) =
    ((pbcScalarAdjunction c).unit.app (P.X i)).val.app U x
  erw [(pbcRestrictComp_exists a b c h).exists.choose_spec]
  erw [(pbcScalarAdjunction_exists a).exists.choose_spec,
    (pbcScalarAdjunction_exists b).exists.choose_spec,
    (pbcScalarAdjunction_exists c).exists.choose_spec]
  change ((reductionBalance T a b c h P).f i).val.app U
    (reductionTensorSection T b ((reductionChange T a).obj (P.X i)) U 1
      (reductionTensorSection T a (P.X i) U 1 x)) =
    reductionTensorSection T c (P.X i) U 1 x
  erw [(reductionBalance_exists T a b c h P).exists.choose_spec.2]
  simp

private theorem restrict_comp_factors
    (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c)
    (P : CochainComplex (proEtaleRingModules T V) ℤ) :
    (pbcDerivedRestrictComp a b c h).hom.app (DerivedCategory.Q.obj P) ≫
      (pbcRestrict c).mapDerivedCategoryFactors.hom.app P =
    (pbcDerivedRestrict a).map ((pbcRestrict b).mapDerivedCategoryFactors.hom.app P) ≫
      (pbcRestrict a).mapDerivedCategoryFactors.hom.app
        (((pbcRestrict b).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (pbcRestrictComp a b c h).hom (.up ℤ)).app P) := by
  dsimp only [pbcDerivedRestrictComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rfl

private theorem scalar_pbc_alias {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :
    scalarExtensionFunctor f T = pbcDerivedExtend (proEtaleConstantRingMap (T := T) f) := by
  rfl
attribute [defeq] scalar_pbc_alias
set_option backward.defeqAttrib.useBackward true

private theorem scalar_pbc_obj_alias {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) (K : proEtaleDerivedCategory T A) :
    (scalarExtensionFunctor f T).obj K =
      (pbcDerivedExtend (proEtaleConstantRingMap (T := T) f)).obj K := by
  rfl
attribute [defeq] scalar_pbc_obj_alias

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] completedAdicDerivedChange completedAdicChange

private theorem scalar_unit_of_models
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂)
    (U₀₁ : C₁ ⥤ C₀) (U₁₂ : C₂ ⥤ C₁) (U₀₂ : C₂ ⥤ C₀)
    {L₀₁ : D₀ ⥤ D₁} {R₀₁ : D₁ ⥤ D₀} (a₀₁ : L₀₁ ⊣ R₀₁)
    {L₁₂ : D₁ ⥤ D₂} {R₁₂ : D₂ ⥤ D₁} (a₁₂ : L₁₂ ⊣ R₁₂)
    {L₀₂ : D₀ ⥤ D₂} {R₀₂ : D₂ ⥤ D₀} (a₀₂ : L₀₂ ⊣ R₀₂)
    (r₀₁ : Q₁ ⋙ R₀₁ ≅ U₀₁ ⋙ Q₀) (r₁₂ : Q₂ ⋙ R₁₂ ≅ U₁₂ ⋙ Q₁)
    (r₀₂ : Q₂ ⋙ R₀₂ ≅ U₀₂ ⋙ Q₀)
    (d : R₁₂ ⋙ R₀₁ ≅ R₀₂)
    (P : C₀) (PA : C₁) (PB PC : C₂)
    (ea : L₀₁.obj (Q₀.obj P) ⟶ Q₁.obj PA)
    (eb : L₁₂.obj (Q₁.obj PA) ⟶ Q₂.obj PB)
    (ec : L₀₂.obj (Q₀.obj P) ⟶ Q₂.obj PC) (hec : IsIso ec)
    (ua : P ⟶ U₀₁.obj PA) (ub : PA ⟶ U₁₂.obj PB) (uc : P ⟶ U₀₂.obj PC)
    (v : U₀₁.obj (U₁₂.obj PB) ⟶ U₀₂.obj PB) (bal : PB ⟶ PC)
    (α : L₁₂.obj (L₀₁.obj (Q₀.obj P)) ⟶ L₀₂.obj (Q₀.obj P))
    (ha : a₀₁.unit.app (Q₀.obj P) ≫ R₀₁.map ea ≫ r₀₁.hom.app PA = Q₀.map ua)
    (hb : a₁₂.unit.app (Q₁.obj PA) ≫ R₁₂.map eb ≫ r₁₂.hom.app PB = Q₁.map ub)
    (hc : a₀₂.unit.app (Q₀.obj P) ≫ R₀₂.map ec ≫ r₀₂.hom.app PC = Q₀.map uc)
    (hd : d.hom.app (Q₂.obj PB) ≫ r₀₂.hom.app PB =
      R₀₁.map (r₁₂.hom.app PB) ≫ r₀₁.hom.app (U₁₂.obj PB) ≫ Q₀.map v)
    (hbal : ua ≫ U₀₁.map ub ≫ v ≫ U₀₂.map bal = uc)
    (hα : α ≫ ec = L₁₂.map ea ≫ eb ≫ Q₂.map bal) :
    a₀₁.unit.app (Q₀.obj P) ≫ R₀₁.map (a₁₂.unit.app (L₀₁.obj (Q₀.obj P))) ≫
      d.hom.app _ ≫ R₀₂.map α = a₀₂.unit.app (Q₀.obj P) := by
  let _ := hec
  apply (cancel_mono (R₀₂.map ec)).mp
  simp only [Category.assoc]
  rw [← Functor.map_comp, hα]
  apply (cancel_mono (r₀₂.hom.app PC)).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [← d.hom.naturality_assoc (L₁₂.map ea)]
  change a₀₁.unit.app _ ≫ R₀₁.map (a₁₂.unit.app _) ≫
    R₀₁.map (R₁₂.map (L₁₂.map ea)) ≫ _ = _
  have hu := a₁₂.unit.naturality ea
  dsimp only [Functor.comp_map, Functor.id_map] at hu
  rw [← R₀₁.map_comp_assoc, ← hu]
  simp only [Functor.map_comp, Category.assoc]
  rw [← d.hom.naturality_assoc eb]
  have hrn := r₀₂.hom.naturality bal
  dsimp only [Functor.comp_map] at hrn
  rw [hrn, reassoc_of% hd]
  simp only [Functor.comp_map]
  have hbm := congrArg R₀₁.map hb
  simp only [Functor.map_comp] at hbm
  rw [reassoc_of% hbm]
  have hrn₁ := r₀₁.hom.naturality ub
  dsimp only [Functor.comp_map] at hrn₁
  rw [reassoc_of% hrn₁, reassoc_of% ha, hc]
  rw [← Q₀.map_comp, ← Q₀.map_comp, ← Q₀.map_comp, hbal]

private theorem scalar_composition_unit_model
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (a : A →+* B) (b : B →+* C) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat P)
    (hPB : CochainComplex.IsAcyclicTensorKFlat
      ((reductionChangeComplex T (proEtaleConstantRingMap (T := T) a)).obj P)) :
    (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := T) a)).unit.app
        (DerivedCategory.Q.obj P) ≫
      (pbcDerivedRestrict (proEtaleConstantRingMap (T := T) a)).map
        ((pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := T) b)).unit.app
          ((scalarExtensionFunctor a T).obj (DerivedCategory.Q.obj P))) ≫
      (pbcDerivedRestrictComp
        (proEtaleConstantRingMap (T := T) a) (proEtaleConstantRingMap (T := T) b)
        (proEtaleConstantRingMap (T := T) (b.comp a))
        (scalarExtensionFunctor_ringMap_comp a b T)).hom.app _ ≫
      (pbcDerivedRestrict (proEtaleConstantRingMap (T := T) (b.comp a))).map
        ((scalarExtensionFunctor_composition a b T).hom.app (DerivedCategory.Q.obj P)) =
      (pbcDerivedScalarAdjunction
        (proEtaleConstantRingMap (T := T) (b.comp a))).unit.app
          (DerivedCategory.Q.obj P) := by
  let ac := proEtaleConstantRingMap (T := T) a
  let bc := proEtaleConstantRingMap (T := T) b
  let cc := proEtaleConstantRingMap (T := T) (b.comp a)
  let h := scalarExtensionFunctor_ringMap_comp a b T
  exact scalar_unit_of_models
    DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    ((pbcRestrict ac).mapHomologicalComplex (.up ℤ))
    ((pbcRestrict bc).mapHomologicalComplex (.up ℤ))
    ((pbcRestrict cc).mapHomologicalComplex (.up ℤ))
    (pbcDerivedScalarAdjunction ac) (pbcDerivedScalarAdjunction bc)
    (pbcDerivedScalarAdjunction cc)
    (pbcRestrict ac).mapDerivedCategoryFactors
    (pbcRestrict bc).mapDerivedCategoryFactors
    (pbcRestrict cc).mapDerivedCategoryFactors
    (pbcDerivedRestrictComp ac bc cc h)
    P ((reductionChangeComplex T ac).obj P)
    ((reductionChangeComplex T bc).obj ((reductionChangeComplex T ac).obj P))
    ((reductionChangeComplex T cc).obj P)
    (scalarExtensionFunctorCounit a T P)
    (scalarExtensionFunctorCounit b T ((reductionChangeComplex T ac).obj P))
    (scalarExtensionFunctorCounit (b.comp a) T P)
    (scalarExtensionFunctor_kflat_representation (b.comp a) T P hP)
    ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction ac).unit (.up ℤ)).app P)
    ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction bc).unit (.up ℤ)).app
      ((reductionChangeComplex T ac).obj P))
    ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction cc).unit (.up ℤ)).app P)
    ((NatTrans.mapHomologicalComplex (pbcRestrictComp ac bc cc h).hom (.up ℤ)).app _)
    (reductionBalance T ac bc cc h P)
    ((scalarExtensionFunctor_composition a b T).hom.app (DerivedCategory.Q.obj P))
    ((pbcDerivedScalarAdjunction_exists ac).exists.choose_spec P hP)
    ((pbcDerivedScalarAdjunction_exists bc).exists.choose_spec _ hPB)
    ((pbcDerivedScalarAdjunction_exists cc).exists.choose_spec P hP)
    (restrict_comp_factors T ac bc cc h _)
    (balance_unit T ac bc cc h P)
    ((scalarExtensionFunctor_composition_existsUnique a b T).exists.choose_spec P hP)
private theorem natTrans_ext_kflat
    (T : Scheme.{u}) (A : Type u) [CommRing A]
    {D : Type*} [Category* D]
    {F G : proEtaleDerivedCategory T A ⥤ D} (α β : F ⟶ G)
    (h : ∀ (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ),
      CochainComplex.IsAcyclicTensorKFlat P →
      (∀ i : ℤ, exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _
          (SheafOfModules.monoidalCategory (proEtaleConstantRing T A)) (P.X i))) →
      α.app (DerivedCategory.Q.obj P) = β.app (DerivedCategory.Q.obj P)) : α = β := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  ext K
  let L := DerivedCategory.Q.objPreimage K
  obtain ⟨P, f, hP, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients L
  have : QuasiIso f := hq
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  apply (cancel_epi (F.map e.hom)).1
  rw [α.naturality, β.naturality, h P hP hf]

private def change_model_iso
    (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)
    (E : proEtaleRingModules T R ⥤ proEtaleRingModules T S) [E.Additive]
    (hobj : ∀ M, E.obj M = SheafOfModules.changeOfRings a M)
    (hmap : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom a M f ≫ eqToHom (hobj N).symm)
    (P : CochainComplex (proEtaleRingModules T R) ℤ) :
    (E.mapHomologicalComplex (.up ℤ)).obj P ≅
      SheafOfModules.changeOfRingsComplex.{u + 1, u} a P :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ eqToIso (hobj (P.X i))) (by
    intro i j hij
    change eqToHom (hobj (P.X i)) ≫
      SheafOfModules.changeOfRingsHom a (P.X i) (P.d i j) =
      E.map (P.d i j) ≫ eqToHom (hobj (P.X j))
    rw [hmap]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])

private theorem scalar_composition_unit
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (a : A →+* B) (b : B →+* C) (T : Scheme.{u})
    (K : proEtaleDerivedCategory T A) :
    (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := T) a)).unit.app K ≫
      (pbcDerivedRestrict (proEtaleConstantRingMap (T := T) a)).map
        ((pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := T) b)).unit.app
          ((scalarExtensionFunctor a T).obj K)) ≫
      (pbcDerivedRestrictComp
        (proEtaleConstantRingMap (T := T) a) (proEtaleConstantRingMap (T := T) b)
        (proEtaleConstantRingMap (T := T) (b.comp a))
        (scalarExtensionFunctor_ringMap_comp a b T)).hom.app _ ≫
      (pbcDerivedRestrict (proEtaleConstantRingMap (T := T) (b.comp a))).map
        ((scalarExtensionFunctor_composition a b T).hom.app K) =
      (pbcDerivedScalarAdjunction
        (proEtaleConstantRingMap (T := T) (b.comp a))).unit.app K := by
  let ac := proEtaleConstantRingMap (T := T) a
  let bc := proEtaleConstantRingMap (T := T) b
  let cc := proEtaleConstantRingMap (T := T) (b.comp a)
  let adj := (pbcDerivedScalarAdjunction ac).comp (pbcDerivedScalarAdjunction bc)
  let lhs := adj.unit ≫
    Functor.whiskerLeft (scalarExtensionFunctor a T ⋙ scalarExtensionFunctor b T)
      (pbcDerivedRestrictComp ac bc cc (scalarExtensionFunctor_ringMap_comp a b T)).hom ≫
    Functor.whiskerRight (scalarExtensionFunctor_composition a b T).hom (pbcDerivedRestrict cc)
  have heq : lhs = (pbcDerivedScalarAdjunction cc).unit := by
    apply natTrans_ext_kflat T A
    intro P hP hflat
    have hPB := (SheafOfModules.changeOfRings_isKFlat_of_flat_terms ac P hP hflat).1
    have hobj (M : proEtaleRingModules T (proEtaleConstantRing T A)) :
        (reductionChange T ac).obj M = SheafOfModules.changeOfRings ac M :=
      proEtaleRingExtension_obj ac M
    have hmap {M N : proEtaleRingModules T (proEtaleConstantRing T A)} (f : M ⟶ N) :
        (reductionChange T ac).map f = eqToHom (hobj M) ≫
          SheafOfModules.changeOfRingsHom ac M f ≫ eqToHom (hobj N).symm := by
      unfold reductionChange completedAdicChange
      exact (reductionChangeExistence T ac).choose_spec.choose_spec.choose f
    let e := change_model_iso T ac (reductionChange T ac) hobj hmap P
    have hPB' : CochainComplex.IsAcyclicTensorKFlat ((reductionChangeComplex T ac).obj P) := by
      let := SheafOfModules.monoidalCategory (proEtaleConstantRing T B)
      intro F hF
      let t := HomologicalComplex₂.total.mapIso
        (((MonoidalCategory.curriedTensor _).mapBifunctorHomologicalComplex
          (.up ℤ) (.up ℤ)).obj F |>.mapIso e.symm) (.up ℤ)
      exact (hPB F hF).of_iso t
    simpa only [lhs, adj, ac, bc, cc, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Adjunction.comp_unit_app, Category.assoc,
      Functor.comp_obj, scalarExtensionFunctor, scalarExtension, pbcDerivedExtend,
      proEtaleRingDerivedExtension] using
      scalar_composition_unit_model a b T P hP hPB' 
  have hh := congrArg (fun z ↦ z.app K) heq
  dsimp only [lhs, adj, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Adjunction.comp_unit_app] at hh
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    ac, bc, cc, Adjunction.comp_unit_app, scalarExtensionFunctor, scalarExtension,
    pbcDerivedExtend, proEtaleRingDerivedExtension, Functor.comp_obj, Category.assoc] using hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem left_comp_iso_of_unit
    {D₀ D₁ D₂ : Type*} [Category* D₀] [Category* D₁] [Category* D₂]
    {L₁ : D₀ ⥤ D₁} {R₁ : D₁ ⥤ D₀} {L₂ : D₁ ⥤ D₂} {R₂ : D₂ ⥤ D₁}
    {L₃ : D₀ ⥤ D₂} {R₃ : D₂ ⥤ D₀}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (d : R₂ ⋙ R₁ ≅ R₃) (α : L₁ ⋙ L₂ ≅ L₃)
    (h : ∀ X, (a₁.comp a₂).unit.app X ≫ d.hom.app _ ≫
      R₃.map (α.hom.app X) = a₃.unit.app X) :
    α = Adjunction.leftAdjointCompIso a₁ a₂ a₃ d := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply ((a₁.comp a₂).homEquiv X _).injective
  simp only [Adjunction.homEquiv_unit]
  apply (cancel_mono (d.hom.app (L₃.obj X))).1
  have hn := d.hom.naturality (α.hom.app X)
  rw [Category.assoc, hn, h]
  have hc := unit_conjugateEquiv_symm a₃ (a₁.comp a₂) d.inv X
  rw [Adjunction.leftAdjointCompIso_hom, Adjunction.leftAdjointCompNatTrans]
  rw [← hc, Category.assoc, d.inv_hom_id_app]
  exact (Category.comp_id (a₃.unit.app X)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_composition_is_mate
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (a : A →+* B) (b : B →+* C) (T : Scheme.{u}) :
    scalarExtensionFunctor_composition a b T =
      Adjunction.leftAdjointCompIso
        (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := T) a))
        (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := T) b))
        (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := T) (b.comp a)))
        (pbcDerivedRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp a b T)) := by
  apply left_comp_iso_of_unit
  intro K
  simpa only [Adjunction.comp_unit_app, Functor.comp_obj, Category.assoc,
    scalarExtensionFunctor, scalarExtension, pbcDerivedExtend,
    proEtaleRingDerivedExtension] using scalar_composition_unit a b T K


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped CategoryTheory.TwoSquare

private abbrev ringRestrictionPush
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y) :=
  proEtaleRingRestrictionDirectImage p
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
    (proEtaleConstantRingComparison p A) (proEtaleConstantRingComparison p B)
    (proEtaleConstantInverseImageMap_naturality p
      (CommRingCat.ofHom (RingHom.ulift φ))).symm

private theorem ringRestrictionPush_sections
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (N : proEtaleRingModules Z (proEtaleConstantRing Z B))
    (W : Y.ProEtᵒᵖ) (x : N.val.obj ((proEtaleBaseChange p).op.obj W)) :
    ((ringRestrictionPush φ p).hom.app N).val.app W x = x :=
  (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique p
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
    (proEtaleConstantRingComparison p A) (proEtaleConstantRingComparison p B)
    (proEtaleConstantInverseImageMap_naturality p
      (CommRingCat.ofHom (RingHom.ulift φ))).symm)).1 N W x

private theorem ringRestrictionPush_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (N : proEtaleRingModules Z (proEtaleConstantRing Z C)) :
    (pbcRestrictComp (proEtaleConstantRingMap (T := Y) φ)
        (proEtaleConstantRingMap (T := Y) ψ)
        (proEtaleConstantRingMap (T := Y) (ψ.comp φ))
        (scalarExtensionFunctor_ringMap_comp φ ψ Y)).hom.app
          ((proEtaleConstantRingPushforward C p).obj N) ≫
      (ringRestrictionPush (ψ.comp φ) p).hom.app N =
    (pbcRestrict (proEtaleConstantRingMap (T := Y) φ)).map
        ((ringRestrictionPush ψ p).hom.app N) ≫
      (ringRestrictionPush φ p).hom.app
        ((pbcRestrict (proEtaleConstantRingMap (T := Z) ψ)).obj N) ≫
      (proEtaleConstantRingPushforward A p).map
        ((pbcRestrictComp (proEtaleConstantRingMap (T := Z) φ)
          (proEtaleConstantRingMap (T := Z) ψ)
          (proEtaleConstantRingMap (T := Z) (ψ.comp φ))
          (scalarExtensionFunctor_ringMap_comp φ ψ Z)).hom.app N) := by
  ext W x
  change ((ringRestrictionPush (ψ.comp φ) p).hom.app N).val.app W
      (((pbcRestrictComp (proEtaleConstantRingMap (T := Y) φ)
        (proEtaleConstantRingMap (T := Y) ψ)
        (proEtaleConstantRingMap (T := Y) (ψ.comp φ))
        (scalarExtensionFunctor_ringMap_comp φ ψ Y)).hom.app _).val.app W x) = _
  erw [ringRestrictionPush_sections,
    (pbcRestrictComp_exists _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ Y)).exists.choose_spec]
  change x = ((pbcRestrictComp (proEtaleConstantRingMap (T := Z) φ)
    (proEtaleConstantRingMap (T := Z) ψ)
    (proEtaleConstantRingMap (T := Z) (ψ.comp φ))
    (scalarExtensionFunctor_ringMap_comp φ ψ Z)).hom.app N).val.app
      ((proEtaleBaseChange p).op.obj W)
      (((ringRestrictionPush φ p).hom.app
        ((pbcRestrict (proEtaleConstantRingMap (T := Z) ψ)).obj N)).val.app W
        (((ringRestrictionPush ψ p).hom.app N).val.app W x))
  erw [(pbcRestrictComp_exists _ _ _
    (scalarExtensionFunctor_ringMap_comp φ ψ Z)).exists.choose_spec,
    ringRestrictionPush_sections, ringRestrictionPush_sections]

private theorem mate_cocycle_converse
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category* A₀] [Category* A₁] [Category* A₂]
    [Category* B₀] [Category* B₁] [Category* B₂]
    {L₀ : A₀ ⥤ B₀} {R₀ : B₀ ⥤ A₀} (a₀ : L₀ ⊣ R₀)
    {L₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ A₁} (a₁ : L₁ ⊣ R₁)
    {L₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ A₂} (a₂ : L₂ ⊣ R₂)
    (U₀₁ : A₀ ⥤ A₁) (U₁₂ : A₁ ⥤ A₂) (U₀₂ : A₀ ⥤ A₂)
    (T₀₁ : B₀ ⥤ B₁) (T₁₂ : B₁ ⥤ B₂) (T₀₂ : B₀ ⥤ B₂)
    (αA : U₀₁ ⋙ U₁₂ ⟶ U₀₂) (αB : T₀₁ ⋙ T₁₂ ⟶ T₀₂)
    (lm₀₁ : U₀₁ ⋙ L₁ ⟶ L₀ ⋙ T₀₁) (lm₁₂ : U₁₂ ⋙ L₂ ⟶ L₁ ⋙ T₁₂)
    (lm₀₂ : U₀₂ ⋙ L₂ ⟶ L₀ ⋙ T₀₂)
    (γ₀₁ : R₀ ⋙ U₀₁ ⟶ T₀₁ ⋙ R₁) (γ₁₂ : R₁ ⋙ U₁₂ ⟶ T₁₂ ⋙ R₂)
    (γ₀₂ : R₀ ⋙ U₀₂ ⟶ T₀₂ ⋙ R₂)
    (h₀₁ : ∀ K, U₀₁.map (a₀.unit.app K) ≫ γ₀₁.app (L₀.obj K) =
      a₁.unit.app (U₀₁.obj K) ≫ R₁.map (lm₀₁.app K))
    (h₁₂ : ∀ K, U₁₂.map (a₁.unit.app K) ≫ γ₁₂.app (L₁.obj K) =
      a₂.unit.app (U₁₂.obj K) ≫ R₂.map (lm₁₂.app K))
    (h₀₂ : ∀ K, U₀₂.map (a₀.unit.app K) ≫ γ₀₂.app (L₀.obj K) =
      a₂.unit.app (U₀₂.obj K) ≫ R₂.map (lm₀₂.app K))
    (hγ : ∀ N, αA.app (R₀.obj N) ≫ γ₀₂.app N =
      U₁₂.map (γ₀₁.app N) ≫ γ₁₂.app (T₀₁.obj N) ≫ R₂.map (αB.app N))
    (K : A₀) :
    L₂.map (αA.app K) ≫ lm₀₂.app K =
      lm₁₂.app (U₀₁.obj K) ≫ T₁₂.map (lm₀₁.app K) ≫ αB.app (L₀.obj K) := by
  apply (a₂.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_obj]
  have hu := a₂.unit.naturality (αA.app K)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at hu
  rw [← Category.assoc, ← hu]
  simp only [Category.assoc]
  rw [← h₀₂]
  have hn := αA.naturality (a₀.unit.app K)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hn
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc]
  rw [hγ]
  rw [← Category.assoc (U₁₂.map (U₀₁.map (a₀.unit.app K))), ← U₁₂.map_comp, h₀₁]
  simp only [Functor.map_comp, Category.assoc]
  have hg := γ₁₂.naturality (lm₀₁.app K)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hg
  rw [← Category.assoc (U₁₂.map (R₁.map (lm₀₁.app K))), hg]
  rw [← Category.assoc, ← Category.assoc, h₁₂]
  simp only [Category.assoc]


private abbrev ringRestrictionPullInv
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y) :=
  proEtaleRingRestrictionPullbackInv p
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
    (proEtaleConstantRingComparison p A) (proEtaleConstantRingComparison p B)
    (proEtaleConstantInverseImageMap_naturality p
      (CommRingCat.ofHom (RingHom.ulift φ))).symm

private theorem ringRestrictionPull_unit
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (K : proEtaleRingModules Y (proEtaleConstantRing Y B)) :
    (pbcRestrict (proEtaleConstantRingMap (T := Y) φ)).map
        ((proEtaleConstantRingAdjunction B p).unit.app K) ≫
      (ringRestrictionPush φ p).hom.app
        ((proEtaleConstantRingPullback B p).obj K) =
    (proEtaleConstantRingAdjunction A p).unit.app
        ((pbcRestrict (proEtaleConstantRingMap (T := Y) φ)).obj K) ≫
      (proEtaleConstantRingPushforward A p).map ((ringRestrictionPullInv φ p).app K) := by
  let α := TwoSquare.mk _ _ _ _ (ringRestrictionPush φ p).hom
  have h := unit_mateEquiv_symm (proEtaleConstantRingAdjunction B p)
    (proEtaleConstantRingAdjunction A p) α K
  simp only [α, mateEquiv_symm_apply, ringRestrictionPullInv,
    proEtaleRingRestrictionPullbackInv, proEtaleRingRestrictionPullbackApp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Functor.comp_obj,
    Functor.comp_map, TwoSquare.mk, TwoSquare.natTrans, Category.id_comp,
    CategoryTheory.Functor.map_id] at h ⊢
  simpa only [Category.comp_id, Functor.id_obj] using h

private theorem ringRestrictionPull_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (K : proEtaleRingModules Y (proEtaleConstantRing Y C)) :
    (proEtaleConstantRingPullback A p).map
        ((pbcRestrictComp (proEtaleConstantRingMap (T := Y) φ)
          (proEtaleConstantRingMap (T := Y) ψ)
          (proEtaleConstantRingMap (T := Y) (ψ.comp φ))
          (scalarExtensionFunctor_ringMap_comp φ ψ Y)).hom.app K) ≫
      (ringRestrictionPullInv (ψ.comp φ) p).app K =
    (ringRestrictionPullInv φ p).app
        ((pbcRestrict (proEtaleConstantRingMap (T := Y) ψ)).obj K) ≫
      (pbcRestrict (proEtaleConstantRingMap (T := Z) φ)).map
        ((ringRestrictionPullInv ψ p).app K) ≫
      (pbcRestrictComp (proEtaleConstantRingMap (T := Z) φ)
        (proEtaleConstantRingMap (T := Z) ψ)
        (proEtaleConstantRingMap (T := Z) (ψ.comp φ))
        (scalarExtensionFunctor_ringMap_comp φ ψ Z)).hom.app
          ((proEtaleConstantRingPullback C p).obj K) := by
  exact mate_cocycle_converse
    (proEtaleConstantRingAdjunction C p) (proEtaleConstantRingAdjunction B p)
    (proEtaleConstantRingAdjunction A p)
    (pbcRestrict (proEtaleConstantRingMap (T := Y) ψ))
    (pbcRestrict (proEtaleConstantRingMap (T := Y) φ))
    (pbcRestrict (proEtaleConstantRingMap (T := Y) (ψ.comp φ)))
    (pbcRestrict (proEtaleConstantRingMap (T := Z) ψ))
    (pbcRestrict (proEtaleConstantRingMap (T := Z) φ))
    (pbcRestrict (proEtaleConstantRingMap (T := Z) (ψ.comp φ)))
    (pbcRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ Y)).hom
    (pbcRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ Z)).hom
    (ringRestrictionPullInv ψ p) (ringRestrictionPullInv φ p)
    (ringRestrictionPullInv (ψ.comp φ) p)
    (ringRestrictionPush ψ p).hom (ringRestrictionPush φ p).hom
    (ringRestrictionPush (ψ.comp φ) p).hom
    (ringRestrictionPull_unit ψ p) (ringRestrictionPull_unit φ p)
    (ringRestrictionPull_unit (ψ.comp φ) p) (ringRestrictionPush_comp φ ψ p) K


private abbrev ringRestrictionPullIso
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y) :=
  @asIso _ _ _ _ (ringRestrictionPullInv φ p)
    (proEtaleRingRestrictionPullbackInv_isIso p
      (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
      (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
      (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
      (proEtaleConstantRingComparison p A) (proEtaleConstantRingComparison p B)
      (proEtaleConstantInverseImageMap_naturality p
        (CommRingCat.ofHom (RingHom.ulift φ))).symm)

private theorem ringRestrictionPull_inv_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (K : proEtaleRingModules Y (proEtaleConstantRing Y C)) :
    (ringRestrictionPullIso (ψ.comp φ) p).inv.app K ≫
      (proEtaleConstantRingPullback A p).map
        ((pbcRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ Y)).inv.app K) =
    (pbcRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ Z)).inv.app
        ((proEtaleConstantRingPullback C p).obj K) ≫
      (pbcRestrict (proEtaleConstantRingMap (T := Z) φ)).map
        ((ringRestrictionPullIso ψ p).inv.app K) ≫
      (ringRestrictionPullIso φ p).inv.app
        ((pbcRestrict (proEtaleConstantRingMap (T := Y) ψ)).obj K) := by
  let dY := pbcRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ Y)
  let dZ := pbcRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ Z)
  have he :
      (proEtaleConstantRingPullback A p).mapIso (dY.app K) ≪≫
        (ringRestrictionPullIso (ψ.comp φ) p).app K =
      (ringRestrictionPullIso φ p).app
          ((pbcRestrict (proEtaleConstantRingMap (T := Y) ψ)).obj K) ≪≫
        (pbcRestrict (proEtaleConstantRingMap (T := Z) φ)).mapIso
          ((ringRestrictionPullIso ψ p).app K) ≪≫
        dZ.app ((proEtaleConstantRingPullback C p).obj K) := by
    apply Iso.ext
    exact ringRestrictionPull_comp φ ψ p K
  exact congrArg Iso.inv he

private theorem ringRestrictionDerivedPull_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (K : proEtaleDerivedCategory Y C) :
    (Functor.mapDerivedCategorySquareIso
      (ringRestrictionPullIso (ψ.comp φ) p).symm).hom.app K ≫
      (proEtaleConstantRingPullback A p).mapDerivedCategory.map
        ((Functor.mapDerivedCategoryTriangleIso
          (pbcRestrictComp _ _ _
            (scalarExtensionFunctor_ringMap_comp φ ψ Y)).symm).hom.app K) =
    (Functor.mapDerivedCategoryTriangleIso
      (pbcRestrictComp _ _ _
        (scalarExtensionFunctor_ringMap_comp φ ψ Z)).symm).hom.app
          ((proEtaleConstantRingPullback C p).mapDerivedCategory.obj K) ≫
      (pbcRestrict (proEtaleConstantRingMap (T := Z) φ)).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso
          (ringRestrictionPullIso ψ p).symm).hom.app K) ≫
      (Functor.mapDerivedCategorySquareIso
        (ringRestrictionPullIso φ p).symm).hom.app
          ((pbcRestrict (proEtaleConstantRingMap (T := Y) ψ)).mapDerivedCategory.obj K) := by
  have h := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (ringRestrictionPullIso ψ p).symm (ringRestrictionPullIso φ p).symm
    (ringRestrictionPullIso (ψ.comp φ) p).symm
    (pbcRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ Z)).symm
    (pbcRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ Y)).symm
    (ringRestrictionPull_inv_comp φ ψ p) K
  exact h

private abbrev ringRestrictionDerivedPull
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y) :=
  proEtaleRingRestrictionDerivedPullback p
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
    (proEtaleConstantRingComparison p A) (proEtaleConstantRingComparison p B)
    (proEtaleConstantInverseImageMap_naturality p
      (CommRingCat.ofHom (RingHom.ulift φ))).symm

private theorem ringRestrictionDerivedPull_comp_normalized
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (K : proEtaleDerivedCategory Y C) :
    (ringRestrictionDerivedPull (ψ.comp φ) p).hom.app K ≫
      (proEtaleConstantRingDerivedPullback A p).map
        ((pbcDerivedRestrictComp _ _ _
          (scalarExtensionFunctor_ringMap_comp φ ψ Y)).inv.app K) =
    (pbcDerivedRestrictComp _ _ _
      (scalarExtensionFunctor_ringMap_comp φ ψ Z)).inv.app
        ((proEtaleConstantRingDerivedPullback C p).obj K) ≫
      (pbcDerivedRestrict (proEtaleConstantRingMap (T := Z) φ)).map
        ((ringRestrictionDerivedPull ψ p).hom.app K) ≫
      (ringRestrictionDerivedPull φ p).hom.app
        ((pbcDerivedRestrict (proEtaleConstantRingMap (T := Y) ψ)).obj K) := by
  simpa only [ringRestrictionDerivedPull, ringRestrictionPullIso, ringRestrictionPullInv,
    proEtaleRingRestrictionDerivedPullback,
    Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryTriangleIso,
    pbcDerivedRestrictComp, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Category.assoc, proEtaleConstantRingDerivedPullback, proEtaleConstantRingPullback,
    proEtaleRingDerivedPullback, pbcDerivedRestrict, pbcRestrict] using
    ringRestrictionDerivedPull_comp φ ψ p K

private theorem scalar_mate_comp
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
  [Category* A₀] [Category* A₁] [Category* A₂]
  [Category* B₀] [Category* B₁] [Category* B₂]
  {L₁ : A₀ ⥤ A₁} {R₁ : A₁ ⥤ A₀} {L₂ : A₁ ⥤ A₂} {R₂ : A₂ ⥤ A₁}
  {L₃ : A₀ ⥤ A₂} {R₃ : A₂ ⥤ A₀}
  {l₁ : B₀ ⥤ B₁} {r₁ : B₁ ⥤ B₀} {l₂ : B₁ ⥤ B₂} {r₂ : B₂ ⥤ B₁}
  {l₃ : B₀ ⥤ B₂} {r₃ : B₂ ⥤ B₀}
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
  (b₁ : l₁ ⊣ r₁) (b₂ : l₂ ⊣ r₂) (b₃ : l₃ ⊣ r₃)
  {F₀ : A₀ ⥤ B₀} {F₁ : A₁ ⥤ B₁} {F₂ : A₂ ⥤ B₂}
  (t₁ : TwoSquare R₁ F₁ F₀ r₁) (t₂ : TwoSquare R₂ F₂ F₁ r₂)
  (t₃ : TwoSquare R₃ F₂ F₀ r₃)
  (eA : R₂ ⋙ R₁ ≅ R₃) (eB : r₂ ⋙ r₁ ≅ r₃)
  (h : (t₂ ≫ₕ t₁).whiskerTop eA.inv = t₃.whiskerBottom eB.inv)
 :
    (((mateEquiv a₁ b₁).symm t₁) ≫ᵥ ((mateEquiv a₂ b₂).symm t₂)).whiskerLeft
        (Adjunction.leftAdjointCompIso a₁ a₂ a₃ eA).hom =
    ((mateEquiv a₃ b₃).symm t₃).whiskerRight
        (Adjunction.leftAdjointCompIso b₁ b₂ b₃ eB).hom := by
  apply (mateEquiv a₃ (b₁.comp b₂)).injective
  rw [conjugateEquiv_mateEquiv_vcomp a₃ (a₁.comp a₂) (b₁.comp b₂),
    mateEquiv_conjugateEquiv_vcomp a₃ b₃ (b₁.comp b₂)]
  rw [mateEquiv_hcomp a₁ b₁ a₂ b₂]
  simp only [Equiv.apply_symm_apply, Adjunction.leftAdjointCompIso_hom,
    Adjunction.leftAdjointCompNatTrans]
  exact h


/-- Scalar associativity commutes with the normalized tensor/inverse-image map.
Source: blueprint main-20261015, sk-lem-sp-reduction-direct-image.proof.md,
expanded det-sp-reduction-direct-image, Step 10.
(blueprint: lem-sp-pullback-scalar-coefficient-cocycle).

Proof: choose a flat-term K-flat representative P. Exact geometric pullback preserves
K-flatness, and coefficient extension preserves K-flatness over its target ring.
The universal derived counits therefore identify every functor in this square with
its ordinary tensor/pullback model. The scalar associators are the balanced maps
specified by scalarExtensionFunctor_composition_existsUnique. The inverse-image
comparisons are the inverse mates of the identity-on-sections restriction comparisons,
so their tensor-unit normalizations give the usual balancing maps on these models.
The scalar associator is the conjugate of restriction associativity: the scalar
units send x to 1 tensor x, so the prescribed balancing map respects the composite
unit. The universal counits descend this equation from flat-term K-flat models.
The restriction/direct-image maps are identity on sections and respect composition;
their inverse-image mates and exact derived descent respect the same pasting.
Transpose once more under scalar extension/restriction and cancel the invertible
comparisons. This proves the displayed cocycle. No properness, boundedness or
coefficient flatness is needed. -/
theorem directImageScalarPullbackCoefficientCocycle
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (φ : A →+* B) (ψ : B →+* C)
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) (K : proEtaleDerivedCategory Y A) :
    (proEtaleConstantRingDerivedPullback C p).map
        ((scalarExtensionFunctor_composition φ ψ Y).hom.app K) ≫
      (directImageScalarPullbackIso (ψ.comp φ) p).hom.app K =
    (directImageScalarPullbackIso ψ p).hom.app ((scalarExtensionFunctor φ Y).obj K) ≫
      (scalarExtensionFunctor ψ Z).map ((directImageScalarPullbackIso φ p).hom.app K) ≫
        (scalarExtensionFunctor_composition φ ψ Z).hom.app
          ((proEtaleConstantRingDerivedPullback A p).obj K) := by
  let t₁ := TwoSquare.mk _ _ _ _ (ringRestrictionDerivedPull φ p).inv
  let t₂ := TwoSquare.mk _ _ _ _ (ringRestrictionDerivedPull ψ p).inv
  let t₃ := TwoSquare.mk _ _ _ _ (ringRestrictionDerivedPull (ψ.comp φ) p).inv
  let eA := pbcDerivedRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ Y)
  let eB := pbcDerivedRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ Z)
  have ht : (t₂ ≫ₕ t₁).whiskerTop eA.inv = t₃.whiskerBottom eB.inv := by
    ext X
    dsimp [t₁, t₂, t₃, TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      TwoSquare.mk, TwoSquare.natTrans, eA, eB]
    simp only [Category.id_comp, Category.comp_id]
    apply (cancel_epi ((ringRestrictionDerivedPull (ψ.comp φ) p).hom.app X)).1
    rw [← Category.assoc, ← Category.assoc, ringRestrictionDerivedPull_comp_normalized]
    simp only [pbcDerivedRestrict, pbcRestrict]
    simp [Category.assoc, ← Functor.map_comp]
  have hm := scalar_mate_comp
    (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := Y) φ))
    (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := Y) ψ))
    (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := Y) (ψ.comp φ)))
    (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := Z) φ))
    (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := Z) ψ))
    (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := Z) (ψ.comp φ)))
    t₁ t₂ t₃ eA eB ht
  have hmK := congrArg (fun w ↦ w.natTrans.app K) hm
  dsimp only [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app] at hmK
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at hmK
  dsimp only [eA, eB] at hmK
  rw [← scalar_composition_is_mate φ ψ Y, ← scalar_composition_is_mate φ ψ Z] at hmK
  change (scalarExtensionFunctor ψ Z).map
      ((directImageScalarPullbackIso φ p).inv.app K) ≫
    (directImageScalarPullbackIso ψ p).inv.app ((scalarExtensionFunctor φ Y).obj K) ≫
    (proEtaleConstantRingDerivedPullback C p).map
      ((scalarExtensionFunctor_composition φ ψ Y).hom.app K) =
    (scalarExtensionFunctor_composition φ ψ Z).hom.app
      ((proEtaleConstantRingDerivedPullback A p).obj K) ≫
    (directImageScalarPullbackIso (ψ.comp φ) p).inv.app K at hmK
  apply (cancel_epi ((directImageScalarPullbackIso ψ p).inv.app
    ((scalarExtensionFunctor φ Y).obj K))).1
  apply (cancel_epi ((scalarExtensionFunctor ψ Z).map
    ((directImageScalarPullbackIso φ p).inv.app K))).1
  rw [reassoc_of% hmK]
  simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  change (scalarExtensionFunctor_composition φ ψ Z).hom.app
      ((proEtaleConstantRingDerivedPullback A p).obj K) ≫ 𝟙 _ = _
  exact Category.comp_id _

end AlgebraicGeometry.ProEtale
