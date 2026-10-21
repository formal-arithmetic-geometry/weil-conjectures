/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.SecSmoothPurity.ReductionDirectImageComparison
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero

import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import all Sheaf.SecSmoothPurity.OrdinaryRestrictionPullbackSquare
import all Sheaf.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.Adjunction.ConjugatePaste
import Sheaf.SecSmoothPurity.ScalarAssociatorConjugate
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-!
# Coefficient cocycle for normalized open scalar comparisons

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-direct-image.proof.md, Steps 1 and 4
(blueprint: lem-sp-proetale-open-scalar-cocycle).

The equation uses the prescribed scalar associator and the prescribed comparison for
sectionwise sheafified extension by zero on the full ordinary unbounded categories.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale



open CategoryTheory.Limits CategoryTheory.Functor

private theorem uniqConjugate
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (e : G' ≅ G) :
    a.leftAdjointUniq (b.ofNatIsoRight e) = (conjugateIsoEquiv b a).symm e := by
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app]

private noncomputable abbrev openAdj (A : Type u) [CommRing A]
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :=
  proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing Z A)
    (proEtaleConstantRing U A) (proEtaleConstantRingComparison j A)

private theorem mateTop
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
    {G G' : C₁ ⥤ C₃} {H : C₂ ⥤ C₄}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (w : TwoSquare G' L₁ L₂ H) (t : G ⟶ G') :
    mateEquiv a b (w.whiskerTop t) = (mateEquiv a b w).whiskerRight t := by
  ext d : 1
  simp only [mateEquiv_apply, TwoSquare.whiskerTop, TwoSquare.whiskerRight,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    leftUnitor_hom_app, rightUnitor_inv_app, associator_hom_app,
    associator_inv_app, Functor.map_comp, Category.id_comp, Category.assoc]
  rw [← b.unit_naturality_assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map, TwoSquare.mk, TwoSquare.natTrans]
  simp only [Category.id_comp]

private theorem mateBottom
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
    {G : C₁ ⥤ C₃} {H H' : C₂ ⥤ C₄}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (w : TwoSquare G L₁ L₂ H) (t : H ⟶ H') :
    mateEquiv a b (w.whiskerBottom t) = (mateEquiv a b w).whiskerLeft t := by
  ext d : 1
  simp only [mateEquiv_apply, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    leftUnitor_hom_app, rightUnitor_inv_app, associator_hom_app,
    associator_inv_app, Functor.map_comp, Category.id_comp, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map, TwoSquare.mk, TwoSquare.natTrans]
  simp only [Category.id_comp]
  have ht := congrArg R₂.map (t.naturality (a.counit.app d))
  simp only [Functor.map_comp] at ht
  simpa only [Category.comp_id, Category.id_comp, Category.assoc,
    Functor.comp_obj, Functor.id_obj] using
    congrArg (fun f ↦ b.unit.app (G.obj (R₁.obj d)) ≫
      R₂.map (w.app (R₁.obj d)) ≫ f) ht.symm

attribute [local irreducible] proEtaleRingModulePullback
  proEtaleRingModuleAdjunction proEtaleRingDerivedOpenAdjunction

private theorem restrictionInvApply (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c)
    (M : proEtaleRingModules T V) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp a b c h).inv.app M).val.app U x = x := by
  have hi := congrArg (fun f ↦ f.val.app U x)
    ((pbcRestrictComp a b c h).inv_hom_id_app M)
  change ((pbcRestrictComp a b c h).hom.app M).val.app U
    (((pbcRestrictComp a b c h).inv.app M).val.app U x) = x at hi
  erw [(pbcRestrictComp_exists a b c h).exists.choose_spec] at hi
  exact hi

private theorem ordinaryCoefficientComp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {U Z : Scheme.{u}} (j : U ⟶ Z)
    (M : proEtaleRingModules Z (proEtaleConstantRing Z C)) :
    (ordinaryConstantPullback A j).map
        ((pbcRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ Z)).inv.app M) ≫
      (ordinaryRestrictionComparison φ j).app ((ordinaryScalarRestriction ψ Z).obj M) ≫
      (ordinaryScalarRestriction φ U).map ((ordinaryRestrictionComparison ψ j).app M) =
    (ordinaryRestrictionComparison (ψ.comp φ) j).app M ≫
      (pbcRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ U)).inv.app
        ((ordinaryConstantPullback C j).obj M) := by
  let q := (TwoSquare.mk _ _ _ _ (ordinaryRestrictionComparison ψ j)).hComp
    (TwoSquare.mk _ _ _ _ (ordinaryRestrictionComparison φ j))
  have h : q.whiskerTop
        (pbcRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ Z)).inv =
      (TwoSquare.mk _ _ _ _ (ordinaryRestrictionComparison (ψ.comp φ) j)).whiskerBottom
        (pbcRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ U)).inv := by
    apply (mateEquiv (padj C j) (padj A j)).injective
    rw [mateTop, mateBottom]
    dsimp only [q]
    rw [mateEquiv_vcomp (padj C j) (padj B j) (padj A j)]
    erw [comparison_mate, comparison_mate, comparison_mate]
    ext N : 1
    ext V x
    simp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
      TwoSquare.mk, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id,
      SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
      TwoSquare.natTrans]
    erw [directComparison_apply φ j]
    change ((directComparison ψ j).hom.app N).val.app V
      (((pbcRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ Z)).inv.app
        ((proEtaleRingModuleDirectImage j (proEtaleConstantRing Z C)
          (proEtaleConstantRing U C) (proEtaleConstantRingComparison j C)).obj N)).val.app
            V x) = _
    erw [directComparison_apply ψ j]
    rw [restrictionInvApply]
    have hdc := directComparison_apply (ψ.comp φ) j N V x
    rw [hdc]
    change x = ((pbcRestrictComp _ _ _
      (scalarExtensionFunctor_ringMap_comp φ ψ U)).inv.app N).val.app
        ((proEtaleBaseChange j).op.obj V) x
    exact (restrictionInvApply U _ _ _ _ N _ x).symm
  simpa only [q, TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id]
    using congr_app h M

private local instance ordinaryComparisonIsIso
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U Z : Scheme.{u}} (j : U ⟶ Z) :
    IsIso (ordinaryRestrictionComparison φ j) :=
  proEtaleRingRestrictionPullbackInv_isIso _ _ _ _ _ _ _ _ _ _

private noncomputable def coefficientRightSquare
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U Z : Scheme.{u}} (j : U ⟶ Z) :
    scalarRestriction φ Z ⋙ constantPullback (A := A) j ≅
      constantPullback (A := B) j ⋙ scalarRestriction φ U :=
  mapDerivedCategorySquareIso (asIso (ordinaryRestrictionComparison φ j))

private theorem derivedCoefficientComp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {U Z : Scheme.{u}} (j : U ⟶ Z)
    (M : proEtaleDerivedCategory Z C) :
    (coefficientRightSquare φ j).hom.app ((scalarRestriction ψ Z).obj M) ≫
      (scalarRestriction φ U).map ((coefficientRightSquare ψ j).hom.app M) ≫
      (pbcDerivedRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ U)).hom.app
        ((constantPullback (A := C) j).obj M) =
    (constantPullback (A := A) j).map
        ((pbcDerivedRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ Z)).hom.app M) ≫
      (coefficientRightSquare (ψ.comp φ) j).hom.app M := by
  have hd := exactSquare_comp_forward
    (ordinaryScalarRestriction ψ Z) (ordinaryScalarRestriction φ Z)
    (ordinaryScalarRestriction (ψ.comp φ) Z)
    (ordinaryScalarRestriction ψ U) (ordinaryScalarRestriction φ U)
    (ordinaryScalarRestriction (ψ.comp φ) U)
    (ordinaryConstantPullback C j) (ordinaryConstantPullback B j)
    (ordinaryConstantPullback A j)
    (asIso (ordinaryRestrictionComparison ψ j))
    (asIso (ordinaryRestrictionComparison φ j))
    (asIso (ordinaryRestrictionComparison (ψ.comp φ) j))
    (pbcRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ Z)).symm
    (pbcRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ U)).symm
    (ordinaryCoefficientComp φ ψ j) M
  simp only [mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app] at hd
  change (ordinaryConstantPullback A j).mapDerivedCategory.map
      ((pbcDerivedRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ Z)).inv.app M) ≫
    (coefficientRightSquare φ j).hom.app ((scalarRestriction ψ Z).obj M) ≫
    (scalarRestriction φ U).map ((coefficientRightSquare ψ j).hom.app M) =
    (coefficientRightSquare (ψ.comp φ) j).hom.app M ≫
    (pbcDerivedRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ U)).inv.app
      ((constantPullback (A := C) j).obj M) at hd
  have h := congrArg (fun t ↦
    (constantPullback (A := A) j).map
      ((pbcDerivedRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ Z)).hom.app M) ≫
    t ≫ (pbcDerivedRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ U)).hom.app
      ((constantPullback (A := C) j).obj M)) hd
  simp only [Category.assoc] at h
  change (ordinaryConstantPullback A j).mapDerivedCategory.map _ ≫
    (ordinaryConstantPullback A j).mapDerivedCategory.map _ ≫ _ = _ at h
  erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp] at h
  simp only [Iso.inv_hom_id_app] at h
  erw [Category.comp_id] at h
  exact h

private theorem openConjugate
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :
    conjugateEquiv ((openAdj A j).comp
        (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Z) φ)))
      ((proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := U) φ)).comp
        (openAdj B j)) (openScalarIso φ j).inv =
      (coefficientRightSquare φ j).hom := by
  unfold openScalarIso
  rw [uniqConjugate]
  change (conjugateIsoEquiv _ _
    ((conjugateIsoEquiv _ _).symm _)).inv = _
  rw [Equiv.apply_symm_apply]
  dsimp [proEtaleRingRestrictionDerivedPullback, coefficientRightSquare,
    mapDerivedCategorySquareIso]
  rw [Category.assoc]
  rfl

private theorem normalizedCocycle
    {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [Category A₁] [Category A₂] [Category B₁] [Category B₂]
    [Category C₁] [Category C₂]
    {Oa : A₁ ⥤ A₂} {Ra : A₂ ⥤ A₁} {Ob : B₁ ⥤ B₂} {Rb : B₂ ⥤ B₁}
    {Oc : C₁ ⥤ C₂} {Rc : C₂ ⥤ C₁}
    {Su : A₁ ⥤ B₁} {Ru : B₁ ⥤ A₁} {Sz : A₂ ⥤ B₂} {Rz : B₂ ⥤ A₂}
    {Tu : B₁ ⥤ C₁} {Vu : C₁ ⥤ B₁} {Tz : B₂ ⥤ C₂} {Vz : C₂ ⥤ B₂}
    {Qu : A₁ ⥤ C₁} {Wu : C₁ ⥤ A₁} {Qz : A₂ ⥤ C₂} {Wz : C₂ ⥤ A₂}
    (a : Oa ⊣ Ra) (b : Ob ⊣ Rb) (c : Oc ⊣ Rc)
    (s : Su ⊣ Ru) (s' : Sz ⊣ Rz) (t : Tu ⊣ Vu) (t' : Tz ⊣ Vz)
    (q : Qu ⊣ Wu) (q' : Qz ⊣ Wz)
    (β : Oa ⋙ Sz ≅ Su ⋙ Ob) (γ : Ob ⋙ Tz ≅ Tu ⋙ Oc)
    (δ : Oa ⋙ Qz ≅ Qu ⋙ Oc) (α : Su ⋙ Tu ≅ Qu) (α' : Sz ⋙ Tz ≅ Qz)
    (χ : Rz ⋙ Ra ≅ Rb ⋙ Ru) (χ' : Vz ⋙ Rb ≅ Rc ⋙ Vu)
    (χ'' : Wz ⋙ Ra ≅ Rc ⋙ Wu) (ρ : Vu ⋙ Ru ≅ Wu) (ρ' : Vz ⋙ Rz ≅ Wz)
    (hβ : conjugateEquiv (a.comp s') (s.comp b) β.inv = χ.hom)
    (hγ : conjugateEquiv (b.comp t') (t.comp c) γ.inv = χ'.hom)
    (hδ : conjugateEquiv (a.comp q') (q.comp c) δ.inv = χ''.hom)
    (hα : conjugateEquiv (s.comp t) q α.inv = ρ.hom)
    (hα' : conjugateEquiv (s'.comp t') q' α'.inv = ρ'.hom)
    (h : ∀ K, χ.hom.app (Vz.obj K) ≫ Ru.map (χ'.hom.app K) ≫
      ρ.hom.app (Rc.obj K) = Ra.map (ρ'.hom.app K) ≫ χ''.hom.app K)
    (M : A₁) :
    α'.hom.app (Oa.obj M) ≫ δ.hom.app M =
      Tz.map (β.hom.app M) ≫ γ.hom.app (Su.obj M) ≫ Oc.map (α.hom.app M) := by
  have hh := conjugateEquiv_paste a b c s s' t t' q q' β.inv γ.inv δ.inv
    α.inv α'.inv (by
      rw [hβ, hγ, hδ, hα, hα']
      apply NatTrans.ext
      funext K
      exact h K)
  let e₁ := isoWhiskerLeft Oa α' ≪≫ δ
  let e₂ := isoWhiskerRight β Tz ≪≫ isoWhiskerLeft Su γ ≪≫ isoWhiskerRight α Oc
  have he : e₁ = e₂ := by
    apply Iso.ext_inv
    simpa only [e₁, e₂, Iso.trans_inv, NatTrans.comp_app, isoWhiskerLeft_inv,
      isoWhiskerRight_inv, whiskerLeft_app, whiskerRight_app, Category.assoc]
      using hh.symm
  simpa only [e₁, e₂, Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, Category.assoc]
    using congrArg (fun e ↦ e.hom.app M) he

private theorem transportCocycle
    {A₀ A₁ B₀ B₁ C₀ C₁ : Type*}
    [Category A₀] [Category A₁] [Category B₀] [Category B₁]
    [Category C₀] [Category C₁]
    {J₀ O₀ : A₀ ⥤ A₁} {J₁ O₁ : B₀ ⥤ B₁} {J₂ O₂ : C₀ ⥤ C₁}
    {S₀ : A₀ ⥤ B₀} {S₁ : A₁ ⥤ B₁} {T₀ : B₀ ⥤ C₀} {T₁ : B₁ ⥤ C₁}
    {V₀ : A₀ ⥤ C₀} {V₁ : A₁ ⥤ C₁}
    (r₀ : J₀ ≅ O₀) (r₁ : J₁ ≅ O₁) (r₂ : J₂ ≅ O₂)
    (b₀ : O₀ ⋙ S₁ ≅ S₀ ⋙ O₁) (b₁ : O₁ ⋙ T₁ ≅ T₀ ⋙ O₂)
    (b₂ : O₀ ⋙ V₁ ≅ V₀ ⋙ O₂)
    (a₀ : S₀ ⋙ T₀ ≅ V₀) (a₁ : S₁ ⋙ T₁ ≅ V₁) (M : A₀)
    (h : a₁.hom.app (O₀.obj M) ≫ b₂.hom.app M =
      T₁.map (b₀.hom.app M) ≫ b₁.hom.app (S₀.obj M) ≫ O₂.map (a₀.hom.app M)) :
    a₁.hom.app (J₀.obj M) ≫
        (isoWhiskerRight r₀ V₁ ≪≫ b₂ ≪≫ isoWhiskerLeft V₀ r₂.symm).hom.app M =
      T₁.map ((isoWhiskerRight r₀ S₁ ≪≫ b₀ ≪≫
        isoWhiskerLeft S₀ r₁.symm).hom.app M) ≫
      (isoWhiskerRight r₁ T₁ ≪≫ b₁ ≪≫
        isoWhiskerLeft T₀ r₂.symm).hom.app (S₀.obj M) ≫ J₂.map (a₀.hom.app M) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  rw [← r₂.inv.naturality]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.map_comp, Category.assoc]
  erw [T₁.map_id]
  simp only [Category.id_comp]
  rw [← reassoc_of% h]
  simpa only [Functor.comp_map, Category.assoc] using
    (congrArg (fun f ↦ f ≫ b₂.hom.app M ≫ r₂.inv.app _)
      (a₁.hom.naturality (r₀.hom.app M))).symm

/-- The normalized open scalar comparison satisfies the coefficient cocycle.
Source: blueprint main-20261015, sk-lem-sp-reduction-direct-image.proof.md, Steps 1 and 4
(blueprint: lem-sp-proetale-open-scalar-cocycle).

Proof:
1. Use the normalized scalar adjunctions of
   lem-pur-sheaf-ring-derived-coefficient-adjunction and the open adjunctions of
   def-sp-reduction-direct-image-comparison, composing them by
   def-weil-pbc-composite-adjunction. The right conjugate of the open comparison beta
   is the restriction/pullback comparison chi of lem-weil-pbc-ring-sheaf-change-adjunction.
2. Restriction along A -> B -> C leaves sections unchanged and gives the action through
   the composite ring map (def-pc-sheaf-restrict-scalars). Both coefficient/pullback
   pastings are the identity on the inverse-image abelian sheaf. Descend this equality
   termwise by lem-weil-pbc-localization-universal-property, including its canonical
   rebracketing comparisons.
3. The unit normalization of lem-sfb-successive-derived-quotient-normalization and
   uniqueness in lem-weil-pbc-conjugate-iso-unit-equation identify the right conjugate
   of the specified scalar associator of det-sp-scalar-extension-functor with the
   restriction-composition comparison rho, at both U and Z.
4. Apply lem-weil-pbc-mate-pasting to both composites with beta. Their right conjugates
   are the two equal pastings of Step 2. Injectivity of def-weil-pbc-adjunction-conjugate
   gives the equality in the normalized left-adjoint coordinates.
5. Expand each prescribed e as S(r_A), then beta, then inverse r_B, using
   def-sp-reduction-direct-image-comparison. The two intermediate r_B factors cancel
   by functoriality. Naturality of r_C moves the scalar associator past its inverse;
   Step 4 replaces the middle three maps. Naturality of the specified scalar associator
   (det-sp-scalar-extension-functor) moves it past r_A, giving the direct e followed
   after alpha, exactly the displayed equation. This works for empty opens, unbounded
   objects and nonflat coefficient maps alike.
-/
theorem proEtaleOpenScalarCocycle
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)
    (hB : ∃ n : ℕ, (ℓ : B) ^ n = 0)
    (hC : ∃ n : ℕ, (ℓ : C) ^ n = 0)
    (φ : A →+* B) (ψ : B →+* C)
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (M : proEtaleDerivedCategory U A) :
    (scalarExtensionFunctor_composition φ ψ Z).hom.app
        ((sfIntrinsicExtensionByZero j A).mapDerivedCategory.obj M) ≫
      (reductionOpenScalarIso (ψ.comp φ) j).hom.app M =
    (scalarExtensionFunctor ψ Z).map ((reductionOpenScalarIso φ j).hom.app M) ≫
      (reductionOpenScalarIso ψ j).hom.app ((scalarExtensionFunctor φ U).obj M) ≫
      (sfIntrinsicExtensionByZero j C).mapDerivedCategory.map
        ((scalarExtensionFunctor_composition φ ψ U).hom.app M) := by
  -- The categorical cocycle below also holds without the torsion hypotheses.
  have _ := hℓ
  have _ := hA
  have _ := hB
  have _ := hC
  have hbeta :
      (scalarExtensionFunctor_composition φ ψ Z).hom.app ((openExtension j).obj M) ≫
        (openScalarIso (ψ.comp φ) j).hom.app M =
      (scalarExtensionFunctor ψ Z).map ((openScalarIso φ j).hom.app M) ≫
        (openScalarIso ψ j).hom.app ((scalarExtensionFunctor φ U).obj M) ≫
        (openExtension j).map ((scalarExtensionFunctor_composition φ ψ U).hom.app M) := by
    apply normalizedCocycle (openAdj A j) (openAdj B j) (openAdj C j)
      (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := U) φ))
      (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Z) φ))
      (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := U) ψ))
      (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Z) ψ))
      (proEtaleRingDerivedExtensionAdjunction
        (proEtaleConstantRingMap (T := U) (ψ.comp φ)))
      (proEtaleRingDerivedExtensionAdjunction
        (proEtaleConstantRingMap (T := Z) (ψ.comp φ)))
      (openScalarIso φ j) (openScalarIso ψ j) (openScalarIso (ψ.comp φ) j)
      (scalarExtensionFunctor_composition φ ψ U) (scalarExtensionFunctor_composition φ ψ Z)
      (coefficientRightSquare φ j) (coefficientRightSquare ψ j)
      (coefficientRightSquare (ψ.comp φ) j)
      (pbcDerivedRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ U))
      (pbcDerivedRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ Z))
      (openConjugate φ j) (openConjugate ψ j) (openConjugate (ψ.comp φ) j) ?_ ?_
      (derivedCoefficientComp φ ψ j) M
    all_goals exact scalarAssociatorConjugate φ ψ _
  exact transportCocycle (reductionOpenModel A j) (reductionOpenModel B j)
    (reductionOpenModel C j) (openScalarIso φ j) (openScalarIso ψ j)
    (openScalarIso (ψ.comp φ) j) (scalarExtensionFunctor_composition φ ψ U)
    (scalarExtensionFunctor_composition φ ψ Z) M hbeta

end AlgebraicGeometry.ProEtale
