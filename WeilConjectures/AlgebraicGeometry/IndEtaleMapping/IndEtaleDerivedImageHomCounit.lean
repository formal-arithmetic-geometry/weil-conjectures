/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IndEtaleMapping.IndEtaleDerivedImageModel
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.NatIso
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp

/-! # Counit identities for the global-Hom adjunction of the derived direct image

The counit normalizations of `imageHomIso`, of restriction and of the coefficient variances of
global Hom, and the compatibility of the constant-pullback comparison with composition.
These are the inputs of `imageHomIso_naturality`.
Source: Bhatt--Scholze 6.3.16, adjunction step; Stacks 08JA
(blueprint: lem-per-ind-etale-derived-image-hom-adjunction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale.IndEtaleMapping

variable (A : Type (u + 1)) [CommRing A]
variable {X : Scheme.{u}} (K M : DerivedCategoryModule A X)


/-- The comparison is the mate of the specified left-adjoint comparison.
This records its counit normalization without any continuity hypothesis.
Source: Stacks 08JA (blueprint: lem-per-ind-etale-derived-image-hom-adjunction).

Proof: apply the counit identity for conjugation of adjunctions to imageTensorIso.
-/
theorem imageHomIso_counit (T : Over X) :
    (ExternalRHom.constant A T.left ⋙
      CategoryTheory.MonoidalCategory.tensorLeft ((ExternalRHom.pull A T.hom).obj K)).map
        (imageHomIso A M K T).hom ≫
      (ExternalRHom.globalAdjunction A ((ExternalRHom.pull A T.hom).obj K)).counit.app
        ((ExternalRHom.pull A T.hom).obj M) =
      (imageTensorIso A K T).hom.app
        (((ExternalRHom.globalHom A X).obj (op K)).obj (imageValue A M T)) ≫
      ((ExternalRHom.globalAdjunction A K).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) T.hom)).counit.app
          ((ExternalRHom.pull A T.hom).obj M) := by
  exact conjugateEquiv_counit
    ((ExternalRHom.globalAdjunction A K).comp
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) T.hom))
    (ExternalRHom.globalAdjunction A ((ExternalRHom.pull A T.hom).obj K))
    (imageTensorIso A K T).hom ((ExternalRHom.pull A T.hom).obj M)

/-- The pulled-back evaluation of a braided transpose, after one braiding, is the evaluation
pushed through the tensor constraint of a braided lax monoidal functor. -/
theorem pulledEvaluation_left
    {C D B : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    [Category* D] [MonoidalCategory D] [BraidedCategory D] [Category* B]
    (F : C ⥤ D) [F.LaxMonoidal] (c : B ⥤ C) (d : B ⥤ D)
    (α : d ≅ c ⋙ F) (E N : C) (Q : B) (ε : E ⊗ c.obj Q ⟶ N)
    (hβ : (β_ (F.obj E) (F.obj (c.obj Q))).hom ≫
      Functor.LaxMonoidal.μ F (c.obj Q) E =
        Functor.LaxMonoidal.μ F E (c.obj Q) ≫ F.map (β_ E (c.obj Q)).hom) :
    (β_ (F.obj E) (d.obj Q)).hom ≫
      ExternalRHom.pullEvaluationOf F c d α (Functor.LaxMonoidal.μ F) E N Q
        ((β_ E (c.obj Q)).inv ≫ ε) =
      (F.obj E ◁ α.hom.app Q) ≫ Functor.LaxMonoidal.μ F E (c.obj Q) ≫ F.map ε := by
  unfold ExternalRHom.pullEvaluationOf
  simp only [Functor.map_comp]
  rw [← BraidedCategory.braiding_naturality_right_assoc]
  dsimp only [Functor.comp_obj]
  rw [reassoc_of% hβ]
  simp only [← F.map_comp_assoc, Iso.hom_inv_id]
  rw [F.map_id, Category.id_comp]

/-- Restriction transposes to pullback of the global tensor-Hom counit.
Source: Bhatt--Scholze 6.3.16, adjunction; Stacks 08JA
(blueprint: lem-per-ind-etale-derived-image-hom-adjunction).

Proof: expand restriction as a transpose. Braided compatibility of inverse image
moves the braiding across its tensor constraint; the two braidings cancel.
-/
theorem imageRestriction_counit (T : Over X) :
    (ExternalRHom.constant A T.left ⋙ tensorLeft ((ExternalRHom.pull A T.hom).obj K)).map
        (ExternalRHom.restriction A T.hom K M) ≫
      (ExternalRHom.globalAdjunction A ((ExternalRHom.pull A T.hom).obj K)).counit.app
        ((ExternalRHom.pull A T.hom).obj M) =
      (imageTensorIso A K T).hom.app
        (((ExternalRHom.globalHom A X).obj (op K)).obj M) ≫
      (ExternalRHom.pull A T.hom).map ((ExternalRHom.globalAdjunction A K).counit.app M) := by
  let := ExternalRHom.derivedBraiding A X
  let := ExternalRHom.derivedBraiding A T.left
  let := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} A) T.hom
  let Q := ((ExternalRHom.globalHom A X).obj (op K)).obj M
  have hb := (leftDerivedUpperStar_μ_map_braiding_hom (ModuleCat.{u + 1} A)
    T.hom K ((ExternalRHom.constant A X).obj Q)).symm
  have h := pulledEvaluation_left (ExternalRHom.pull A T.hom)
    (ExternalRHom.constant A X) (ExternalRHom.constant A T.left)
    (ExternalRHom.constantPullbackIso A T.hom) K M Q
    ((ExternalRHom.globalAdjunction A K).counit.app M) hb
  change ((ExternalRHom.globalAdjunction A
    ((ExternalRHom.pull A T.hom).obj K)).homEquiv _ _).symm
      (ExternalRHom.restriction A T.hom K M) = _
  rw [ExternalRHom.restriction, ExternalRHom.transpose, Equiv.symm_apply_apply]
  simpa only [ExternalRHom.pulledEvaluation, ExternalRHom.evaluation,
    imageTensorIso, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp, Functor.Monoidal.commTensorLeft_hom_app,
    Functor.Monoidal.μIso_hom, Functor.comp_obj, Iso.symm_hom,
    ExternalRHom.pullTensorIso, Q, tensorLeft, curriedTensor, Category.assoc] using h


private theorem hom_counit_naturality
    {C B : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [Category* B] {c : B ⥤ C} {s : C ⥤ B} (a : c ⊣ s)
    {E E' N N' : C} (f : E' ⟶ E) (g : N ⟶ N') :
    (c ⋙ tensorLeft E').map
        (s.map ((MonoidalClosed.pre f).app N) ≫ s.map ((ihom E').map g)) ≫
      (a.comp (MonoidalClosed.internalHomAdjunction₂.adj E')).counit.app N' =
      (f ▷ c.obj (s.obj ((ihom E).obj N))) ≫
        (a.comp (MonoidalClosed.internalHomAdjunction₂.adj E)).counit.app N ≫ g := by
  have h := ExternalRHom.GenericTranspose.ev_naturality a f g
  unfold ExternalRHom.GenericTranspose.ev at h
  have h := congrArg (fun k ↦
    (β_ E' (c.obj (s.obj ((ihom E).obj N)))).hom ≫ k) h
  simp only [Category.assoc] at h
  rw [← BraidedCategory.braiding_naturality_right_assoc] at h
  simp only [Iso.hom_inv_id_assoc] at h
  rw [← BraidedCategory.braiding_naturality_left_assoc] at h
  simpa only [Iso.hom_inv_id_assoc, Functor.comp_map, tensorLeft, curriedTensor] using h

/-- Both coefficient variances of global Hom respect its left-tensor counit.
Source: Stacks 08JA (blueprint: lem-per-ind-etale-derived-image-hom-adjunction).

Proof: the existing evaluation naturality identity gives the square with the
constant coefficient on the left. Naturality of the braiding moves this
coefficient to the right and cancels both inverse braidings.
-/
theorem imageGlobalHom_counit_naturality
    {E E' N N' : DerivedCategoryModule A X} (f : E' ⟶ E) (g : N ⟶ N') :
    (ExternalRHom.constant A X ⋙ tensorLeft E').map
        (((ExternalRHom.globalHom A X).map f.op).app N ≫
          ((ExternalRHom.globalHom A X).obj (op E')).map g) ≫
      (ExternalRHom.globalAdjunction A E').counit.app N' =
      (f ▷ (ExternalRHom.constant A X).obj
        (((ExternalRHom.globalHom A X).obj (op E)).obj N)) ≫
        (ExternalRHom.globalAdjunction A E).counit.app N ≫ g := by
  let := ExternalRHom.derivedBraiding A X
  exact hom_counit_naturality (ExternalRHom.constantSectionsAdjunction A X) f g

section Composition

variable {S T : Scheme.{u}} (f : T ⟶ S) (g : S ⟶ X)

private theorem leftDerivedComp_assoc
    (Z : DerivedCategory (ModuleCat.{u + 1} A)) :
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).leftDerivedFunctorCompIso
      (upperStar (ModuleCat.{u + 1} A) g ⋙ upperStar (ModuleCat.{u + 1} A) f)).hom.app Z ≫
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctorCompIso
        (upperStar (ModuleCat.{u + 1} A) f)).hom.app
          ((ExternalRHom.constant A X).obj Z) =
    (((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⋙
      upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctorCompIso
        (upperStar (ModuleCat.{u + 1} A) f)).hom.app Z ≫
      (ExternalRHom.pull A f).map
        (((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).leftDerivedFunctorCompIso
          (upperStar (ModuleCat.{u + 1} A) g)).hom.app Z) := by
  let F := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let G := upperStar (ModuleCat.{u + 1} A) g
  let H := upperStar (ModuleCat.{u + 1} A) f
  have h := NatTrans.congr_app (Functor.mapDerivedCategoryCompIso_assoc F G H) Z
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  simp only [Functor.leftDerivedFunctorCompIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc,
    Functor.map_comp]
  rw [← NatTrans.naturality_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  simp only [Iso.inv_hom_id_app]
  rw [← NatTrans.naturality_assoc]
  simp only [← Functor.map_comp_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [NatTrans.naturality_assoc]
  erw [H.mapDerivedCategory.map_id]
  rw [Category.id_comp]
  rw [← H.leftDerivedFunctorIsoMapDerivedCategory.inv.naturality]
  rw [← reassoc_of% h]
  rfl


/-- The canonical derived constant comparison respects inverse-image composition.
Source: Stacks 0G7E; Bhatt--Scholze 6.3.16, adjunction
(blueprint: lem-per-ind-etale-derived-image-hom-adjunction).

Proof: transport the underived constant-sheaf composition identity through exact
derivation. Naturality in each functor and associativity of the derived
composition constraints give the displayed equation.
-/
theorem imageConstantPullback_comp
    (Z : DerivedCategory (ModuleCat.{u + 1} A)) :
    (ExternalRHom.constantPullbackIso A (f ≫ g)).hom.app Z ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app
          ((ExternalRHom.constant A X).obj Z) =
      (ExternalRHom.constantPullbackIso A f).hom.app Z ≫
        (ExternalRHom.pull A f).map ((ExternalRHom.constantPullbackIso A g).hom.app Z) := by
  let F := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let G := upperStar (ModuleCat.{u + 1} A) g
  let H := upperStar (ModuleCat.{u + 1} A) f
  let J := upperStar (ModuleCat.{u + 1} A) (f ≫ g)
  let e := (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) g).symm
  let d := (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).symm
  let a := (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) (f ≫ g)).symm
  let b := upperStarComp (ModuleCat.{u + 1} A) f g
  have hi : (a ≪≫ Functor.isoWhiskerLeft F b).symm =
      (d ≪≫ Functor.isoWhiskerRight e H).symm := by
    apply Iso.ext
    apply NatTrans.ext
    funext Q
    apply (cancel_epi (b.hom.app (F.obj Q))).1
    simp only [Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
      Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
      Iso.hom_inv_id_app_assoc]
    exact (Scheme.upperStarConstantSheafIso_comp (ModuleCat.{u + 1} A) f g Q).symm
  have he : a ≪≫ Functor.isoWhiskerLeft F b =
      d ≪≫ Functor.isoWhiskerRight e H := by
    exact congrArg Iso.symm hi
  have hl := congrArg (Functor.leftDerivedFunctorNatIso _ ) he
  simp only [Functor.leftDerivedFunctorNatIso_trans] at hl
  have h₁ := NatTrans.congr_app
    (Functor.leftDerivedFunctorNatIso_isoWhiskerLeft F b) Z
  have h₂ := NatTrans.congr_app
    (Functor.leftDerivedFunctorNatIso_isoWhiskerRight _ e H) Z
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at h₁ h₂
  dsimp only [ExternalRHom.constantPullbackIso, leftDerivedUpperStarComp,
    Iso.trans_hom, NatTrans.comp_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% h₁]
  rw [leftDerivedComp_assoc A f g Z]
  rw [← reassoc_of% h₂]
  have hl' := NatTrans.congr_app (congrArg Iso.hom hl) Z
  simp only [Iso.trans_hom, NatTrans.comp_app] at hl'
  rw [reassoc_of% hl']

end Composition

end AlgebraicGeometry.Etale.IndEtaleMapping
