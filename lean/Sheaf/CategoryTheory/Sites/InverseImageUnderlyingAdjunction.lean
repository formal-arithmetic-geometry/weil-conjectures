/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B8
-/
module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# The underlying inverse-image adjunction on abelian sheaves

Source: Stacks Project, Sites, Proposition 00YV (2).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u₁ v₁ u₂ v₂ w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The abelian adjunction unit is also universal for maps of underlying sheaves of sets.

Source: Stacks Project, Sites, Section 00YR, Proposition 00YV (2).
(blueprint: lem-sfb-site-inverse-image-multimap-universal).

Proof: identify abelian sheaves with commutative group objects. Lift the set adjunction
using preservation of finite products. Restriction computes group operations sectionwise,
so the right lift agrees with abelian direct image. Transport the lifted adjunction and
compare its left adjoint with the chosen abelian inverse image by uniqueness of left
adjoints. The comparison intertwines the units. After forgetting, the lifted unit is
exactly the set adjunction unit; composing with its Hom equivalence and the comparison
isomorphism gives the asserted bijection with the displayed normalization. -/
private theorem site_inverse_image_underlying_hom_bijective
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (U : C ⥤ D)
    [U.IsContinuous J K]
    [(U.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} J K).IsRightAdjoint]
    [PreservesFiniteLimits (U.sheafPullback (Type (max u₁ v₁ u₂ v₂ w)) J K)]
    (F : Sheaf J AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
    (H : Sheaf K (Type (max u₁ v₁ u₂ v₂ w))) :
    Function.Bijective (fun f :
        (sheafCompose K (forget AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})).obj
          ((U.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} J K).obj F) ⟶ H =>
      (sheafCompose J (forget AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})).map
          ((U.sheafAdjunctionContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} J K).unit.app F) ≫
        (U.sheafPushforwardContinuous (Type (max u₁ v₁ u₂ v₂ w)) J K).map f) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
  exact (by
    let : BraidedCategory (Sheaf J (Type (max u₁ v₁ u₂ v₂ w))) :=
      BraidedCategory.ofCartesianMonoidalCategory
    let : BraidedCategory (Sheaf K (Type (max u₁ v₁ u₂ v₂ w))) :=
      BraidedCategory.ofCartesianMonoidalCategory
    let R := U.sheafPushforwardContinuous (Type (max u₁ v₁ u₂ v₂ w)) J K
    let : R.Braided := Functor.Braided.ofChosenFiniteProducts R
    let Rab := U.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} J K
    obtain ⟨FJ, GJ, hFJ, hGJ, hFJGJ, hGJFJ, opJ, _⟩ :=
      sheavesAlgebraicStructuresAbelian.{u₁, v₁, max u₁ v₁ u₂ v₂ w} J
    obtain ⟨FK, GK, hFK, hGK, hFKGK, hGKFK, opK, _⟩ :=
      sheavesAlgebraicStructuresAbelian.{u₂, v₂, max u₁ v₁ u₂ v₂ w} K
    let EJ : Sheaf J AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} ≌
        CommGrp (Sheaf J (Type (max u₁ v₁ u₂ v₂ w))) := {
      functor := FJ
      inverse := GJ
      unitIso := eqToIso hFJGJ.symm
      counitIso := eqToIso hGJFJ
      functor_unitIso_comp := by
        intro X
        simp only [eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans, eqToHom_refl] }
    let EK : Sheaf K AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} ≌
        CommGrp (Sheaf K (Type (max u₁ v₁ u₂ v₂ w))) := {
      functor := FK
      inverse := GK
      unitIso := eqToIso hFKGK.symm
      counitIso := eqToIso hGKFK
      functor_unitIso_comp := by
        intro X
        simp only [eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans, eqToHom_refl] }
    let e : (FK ⋙ R.mapCommGrp) ⋙ CommGrp.forget _ ≅
        (Rab ⋙ FJ) ⋙ CommGrp.forget _ :=
      (Functor.associator FK (CommGrp.forget _) R).symm ≪≫
        Functor.isoWhiskerRight (eqToIso hFK) R ≪≫
        Iso.refl _ ≪≫
        Functor.isoWhiskerLeft Rab (eqToIso hFJ).symm
    have hprod (X Y : Sheaf K (Type (max u₁ v₁ u₂ v₂ w))) :
        (CartesianMonoidalCategory.prodComparisonIso R X Y).inv = 𝟙 _ := by
      have h : (CartesianMonoidalCategory.prodComparisonIso R X Y).hom = 𝟙 _ := by
        rfl
      change (CartesianMonoidalCategory.prodComparisonIso R X Y).inv =
        𝟙 (R.obj (MonoidalCategory.tensorObj X Y))
      simpa only [h, Category.id_comp] using
      (CartesianMonoidalCategory.prodComparisonIso R X Y).hom_inv_id
    have hone : (CartesianMonoidalCategory.preservesTerminalIso R).inv = 𝟙 _ := by
      rfl
    have he (A : Sheaf K AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}) :
        (e.app A).hom ≫ (eqToIso hFJ).hom.app (Rab.obj A) =
          R.map ((eqToIso hFK).hom.app A) := by
      simp [e]
    let egroup : FK ⋙ R.mapCommGrp ≅ Rab ⋙ FJ :=
      NatIso.ofComponents (fun A ↦ CommGrp.mkIso (e.app A) (by
        apply (cancel_mono ((eqToIso hFJ).hom.app (Rab.obj A))).1
        change (Functor.LaxMonoidal.ε R ≫ R.map MonObj.one) ≫
          (e.app A).hom ≫ (eqToIso hFJ).hom.app (Rab.obj A) = _
        rw [Functor.Monoidal.ε_of_cartesianMonoidalCategory, hone, Category.id_comp, he]
        apply Sheaf.hom_ext
        ext X t
        exact (opK A (U.op.obj X)).2.1 t |>.trans
          ((opJ (Rab.obj A) X).2.1 t).symm) (by
        apply (cancel_mono ((eqToIso hFJ).hom.app (Rab.obj A))).1
        change (Functor.LaxMonoidal.μ R _ _ ≫ R.map MonObj.mul) ≫
          (e.app A).hom ≫ (eqToIso hFJ).hom.app (Rab.obj A) = _
        rw [Functor.Monoidal.μ_of_cartesianMonoidalCategory, hprod, Category.id_comp, he]
        apply Sheaf.hom_ext
        ext X ab
        rcases ab with ⟨a, b⟩
        change ((eqToIso hFK).hom.app A).hom.app (U.op.obj X)
          ((MonObj.mul (X := (FK.obj A).X)).hom.app (U.op.obj X) (a, b)) = _
        rw [(opK A (U.op.obj X)).1 a b]
        change _ = ((eqToIso hFJ).hom.app (Rab.obj A)).hom.app X
          ((MonObj.mul (X := (FJ.obj (Rab.obj A)).X)).hom.app X
            (((e.app A).hom.hom.app X) a, ((e.app A).hom.hom.app X) b))
        rw [(opJ (Rab.obj A) X).1]
        have hea (x : (R.obj (FK.obj A).X).obj.obj X) :
            ((eqToIso hFJ).hom.app (Rab.obj A)).hom.app X
                (((e.app A).hom.hom.app X) x) =
              ((eqToIso hFK).hom.app A).hom.app (U.op.obj X) x :=
          congrArg (fun f ↦ f.hom.app X x) (he A)
        rw [hea a, hea b])) (by
        intro A B f
        apply CommGrp.hom_ext
        exact e.hom.naturality f)
    let L := U.sheafPullback (Type (max u₁ v₁ u₂ v₂ w)) J K
    let : L.Braided := Functor.Braided.ofChosenFiniteProducts L
    let adj := U.sheafAdjunctionContinuous (Type (max u₁ v₁ u₂ v₂ w)) J K
    let P := sheafCompose J (forget AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
    let Q := sheafCompose K (forget AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
    let iJ : EJ.functor ⋙ CommGrp.forget _ ≅ P := eqToIso hFJ
    let iK : EK.functor ⋙ CommGrp.forget _ ≅ Q := eqToIso hFK
    let Lt := (EJ.functor ⋙ L.mapCommGrp) ⋙ EK.inverse
    let q : EJ.functor ⋙ L.mapCommGrp ≅ Lt ⋙ EK.functor :=
      (Functor.rightUnitor _).symm ≪≫
        Functor.isoWhiskerLeft (EJ.functor ⋙ L.mapCommGrp) EK.counitIso.symm ≪≫
        (Functor.associator _ _ _).symm
    let aLift : Lt ⊣ Rab := adj.mapCommGrp.restrictFullyFaithful
      EJ.fullyFaithfulFunctor EK.fullyFaithfulFunctor q egroup
    let γ : Lt ⋙ Q ≅ P ⋙ L :=
      Functor.isoWhiskerLeft Lt iK.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight q.symm (CommGrp.forget _) ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft EJ.functor (eqToIso (by rfl)) ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight iJ L
    let aa := U.sheafAdjunctionContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} J K
    let e := aa.leftAdjointUniq aLift
    have ht (A : Sheaf J AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
        (B : Sheaf K AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}) (h : Lt.obj A ⟶ B) :
        P.map (aLift.homEquiv A B h) =
          adj.homEquiv (P.obj A) (Q.obj B) (γ.inv.app A ≫ Q.map h) := by
      have hm : EJ.functor.map (aLift.homEquiv A B h) =
          (adj.mapCommGrp.homEquiv (EJ.functor.obj A) (EK.functor.obj B))
            (q.hom.app A ≫ EK.functor.map h) ≫ egroup.hom.app B := by
        dsimp only [aLift]
        rw [Adjunction.restrictFullyFaithful_homEquiv_apply]
        simp only [Functor.FullyFaithful.map_preimage, Adjunction.homEquiv_unit,
          Functor.map_comp, Category.assoc]
      have hf : (CommGrp.forget _).map
          ((adj.mapCommGrp.homEquiv (EJ.functor.obj A) (EK.functor.obj B))
            (q.hom.app A ≫ EK.functor.map h)) =
          adj.homEquiv (EJ.functor.obj A).X (EK.functor.obj B).X
            ((CommGrp.forget _).map (q.hom.app A ≫ EK.functor.map h)) := by
        rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
        change (𝟙 _ ≫ adj.unit.app _ ≫ 𝟙 _) ≫ R.map _ = _
        simp only [Category.id_comp, Category.comp_id]
        rfl
      have hi := iJ.hom.naturality (aLift.homEquiv A B h)
      dsimp only [Functor.comp_map] at hi
      have hb : (CommGrp.forget _).map (egroup.hom.app B) ≫
          iJ.hom.app (Rab.obj B) = R.map (iK.hom.app B) := he B
      rw [← cancel_epi (iJ.hom.app A), ← hi, hm, Functor.map_comp,
        Category.assoc, hb, hf]
      let x : L.obj (EJ.functor.obj A).X ⟶ (EK.functor.obj B).X :=
        (CommGrp.forget _).map (q.hom.app A ≫ EK.functor.map h)
      change adj.homEquiv _ _ x ≫ R.map (iK.hom.app B) =
        iJ.hom.app A ≫ adj.homEquiv _ _ (γ.inv.app A ≫ Q.map h)
      rw [← adj.homEquiv_naturality_right x (iK.hom.app B)]
      rw [← adj.homEquiv_naturality_left (iJ.hom.app A) (γ.inv.app A ≫ Q.map h)]
      congr 1
      simp only [γ, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
        Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_inv_app, Functor.associator_hom_app, Iso.symm_inv,
        eqToIso.inv, eqToHom_refl, Category.id_comp, Category.assoc]
      simp only [L, NatTrans.id_app, ← Category.assoc, ← Functor.map_comp,
        iJ.hom_inv_id_app, Functor.map_id, Category.id_comp]
      simp only [x, Functor.map_comp, Category.assoc]
      exact congrArg ((CommGrp.forget _).map (q.hom.app A) ≫ ·)
        (iK.hom.naturality h)
    let eL := Functor.isoWhiskerRight e Q ≪≫ γ
    let La := U.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} J K
    have hu : P.map (aa.unit.app F) =
        adj.unit.app (P.obj F) ≫ R.map (eL.inv.app F) := by
      have hh := ht F (La.obj F) (e.inv.app F)
      have hh' : aLift.homEquiv F (La.obj F) (e.inv.app F) = aa.unit.app F := by
        rw [Adjunction.homEquiv_unit]
        change aLift.unit.app F ≫ Rab.map ((aLift.leftAdjointUniq aa).hom.app F) = _
        exact Adjunction.unit_leftAdjointUniq_hom_app aLift aa F
      rw [hh', Adjunction.homEquiv_unit] at hh
      simpa only [eL, Iso.trans_inv, NatTrans.comp_app,
        Functor.isoWhiskerRight_inv, Functor.whiskerRight_app] using hh
    let equiv := (Iso.homCongr (eL.app F) (Iso.refl H)).trans (adj.homEquiv _ H)
    have hequiv (f) : equiv f = P.map (aa.unit.app F) ≫ R.map f := by
      change adj.homEquiv _ H (eL.inv.app F ≫ f ≫ 𝟙 H) = _
      rw [Category.comp_id, Adjunction.homEquiv_unit, hu, R.map_comp, Category.assoc]
    exact (funext hequiv) ▸ equiv.bijective)

/-- A natural map from a finite family of section sets. -/
structure SiteSectionMultimap
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {n : ℕ} (F : Fin n → Sheaf J AddCommGrpCat.{w})
    (H : Sheaf J AddCommGrpCat.{w}) where
  app : ∀ U : C, (∀ i, (F i).obj.obj (Opposite.op U)) → H.obj.obj (Opposite.op U)
  natural : ∀ {U V : C} (f : U ⟶ V) (x : ∀ i, (F i).obj.obj (Opposite.op V)),
    app U (fun i ↦ (F i).obj.map f.op (x i)) = H.obj.map f.op (app V x)

section Products

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {n : ℕ} (F : Fin n → Sheaf J AddCommGrpCat.{w})

private def sectionEvaluation (U : C) : Sheaf J AddCommGrpCat.{w} ⥤ Type w :=
  sheafToPresheaf J AddCommGrpCat.{w} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (Opposite.op U) ⋙ forget AddCommGrpCat.{w}

private instance sectionEvaluation_preservesFiniteLimits (U : C) :
    PreservesFiniteLimits (sectionEvaluation.{u₁, v₁, w} (J := J) U) := by
  dsimp [sectionEvaluation]
  infer_instance

private noncomputable def productSections (U : C) :
    (∏ᶜ F).obj.obj (Opposite.op U) ≃ (∀ i, (F i).obj.obj (Opposite.op U)) :=
  ((PreservesProduct.iso (sectionEvaluation U) F) ≪≫
    Types.productIso (fun i ↦ (F i).obj.obj (Opposite.op U))).toEquiv

private theorem productSections_apply (U : C)
    (x : (∏ᶜ F).obj.obj (Opposite.op U)) (i : Fin n) :
    productSections F U x i = (Pi.π F i).hom.app (Opposite.op U) x := by
  have h : ((PreservesProduct.iso (sectionEvaluation U) F) ≪≫
      Types.productIso (fun i ↦ (F i).obj.obj (Opposite.op U))).hom ≫
        (↾fun x ↦ x i) = (sectionEvaluation U).map (Pi.π F i) := by
    simp only [Iso.trans_hom, Category.assoc, Types.productIso_hom_comp_eval,
      PreservesProduct.iso_hom]
    exact piComparison_comp_π (sectionEvaluation U) F i
  exact ConcreteCategory.congr_hom h x

private theorem productSections_natural {U V : C} (f : U ⟶ V)
    (x : (∏ᶜ F).obj.obj (Opposite.op V)) :
    productSections F U ((∏ᶜ F).obj.map f.op x) =
      fun i ↦ (F i).obj.map f.op (productSections F V x i) := by
  funext i
  simp only [productSections_apply]
  exact ConcreteCategory.congr_hom ((Pi.π F i).hom.naturality f.op) x

private theorem productSections_symm_natural {U V : C} (f : U ⟶ V)
    (x : ∀ i, (F i).obj.obj (Opposite.op V)) :
    (productSections F U).symm (fun i ↦ (F i).obj.map f.op (x i)) =
      (∏ᶜ F).obj.map f.op ((productSections F V).symm x) := by
  apply (productSections F U).injective
  rw [Equiv.apply_symm_apply, productSections_natural, Equiv.apply_symm_apply]

private theorem sectionMultimap_ext {F : Fin n → Sheaf J AddCommGrpCat.{w}}
    {H : Sheaf J AddCommGrpCat.{w}} {a b : SiteSectionMultimap F H}
    (h : ∀ U x, a.app U x = b.app U x) : a = b := by
  cases a
  cases b
  congr
  funext U x
  exact h U x

private noncomputable def multimapHomEquiv (H : Sheaf J AddCommGrpCat.{w}) :
    SiteSectionMultimap F H ≃
      ((sheafCompose J (forget AddCommGrpCat.{w})).obj (∏ᶜ F) ⟶
        (sheafCompose J (forget AddCommGrpCat.{w})).obj H) where
  toFun b := ⟨{
    app := fun U ↦ ↾fun x ↦ b.app U.unop (productSections F U.unop x)
    naturality := by
      intro U V f
      ext x
      change b.app V.unop (productSections F V.unop ((∏ᶜ F).obj.map f x)) = _
      have he := productSections_natural F f.unop x
      simp only [Quiver.Hom.op_unop] at he
      rw [he]
      exact b.natural f.unop _ }⟩
  invFun b := {
    app := fun U x ↦ b.hom.app (Opposite.op U) ((productSections F U).symm x)
    natural := by
      intro U V f x
      rw [productSections_symm_natural]
      exact ConcreteCategory.congr_hom (b.hom.naturality f.op) _ }
  left_inv b := by
    apply sectionMultimap_ext
    intro U x
    change b.app U (productSections F U ((productSections F U).symm x)) = b.app U x
    rw [Equiv.apply_symm_apply]
  right_inv b := by
    apply Sheaf.hom_ext
    ext U x
    exact congrArg (b.hom.app U) ((productSections F U.unop).symm_apply_apply x)

end Products

/-- Restriction along the units is universal for natural maps with finitely many inputs.

Source: Stacks Project, Sites, Section 00YR, Proposition 00YV (2), and Modules on
Sites, Tag 03EL, third equality in the proof of lemma-tensor-product-pullback.
(blueprint: lem-sfb-site-inverse-image-multimap-universal).

Proof: identify abelian sheaves with internal commutative group objects. Lift the
set-valued adjunction by finite-product preservation; restriction computes its
right lift sectionwise. Uniqueness of left adjoints identifies the left lift and
its unit with the chosen abelian inverse image and its unit. Consequently this
unit is universal for underlying set maps, including maps into any underlying
abelian sheaf. Form the finite product of the input sheaves. The abelian inverse
image preserves this product (it is additive); forgetting computes its product
sectionwise. The ordinary set adjunction for that product therefore gives the
asserted unique multimap. Naturality of the unit with each product projection
identifies its coordinates with the individual units, giving precisely the
normalization displayed below. This includes the empty product. -/
theorem site_inverse_image_multimap_universal
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
    [u.IsContinuous J K]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} J K).IsRightAdjoint]
    [PreservesFiniteLimits (u.sheafPullback (Type (max u₁ v₁ u₂ v₂ w)) J K)]
    {n : ℕ} (F : Fin n → Sheaf J AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
    (H : Sheaf K AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
    (b : SiteSectionMultimap F
      ((u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} J K).obj H)) :
    ∃! β : SiteSectionMultimap
        (fun i ↦ (u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} J K).obj (F i)) H,
      ∀ (U : C) (x : ∀ i, (F i).obj.obj (Opposite.op U)),
        β.app (u.obj U) (fun i ↦
          (((u.sheafAdjunctionContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} J K).unit.app
            (F i)).hom.app (Opposite.op U)) (x i)) = b.app U x := by
  let La := u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} J K
  let Ra := u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} J K
  let adj := u.sheafAdjunctionContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} J K
  let R := u.sheafPushforwardContinuous (Type (max u₁ v₁ u₂ v₂ w)) J K
  let P := sheafCompose J (forget AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
  let Q := sheafCompose K (forget AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
  let LF := fun i ↦ La.obj (F i)
  have : Ra.Additive := by
    constructor
    intro A B f g
    rfl
  have : La.Additive := adj.left_adjoint_additive
  let c : Q.obj (La.obj (∏ᶜ F)) ≅ Q.obj (∏ᶜ LF) :=
    Q.mapIso (PreservesProduct.iso La F)
  let e₁ := multimapHomEquiv LF H
  let e₂ := Iso.homCongr c.symm (Iso.refl (Q.obj H))
  let e₃ := multimapHomEquiv F (Ra.obj H)
  let T := fun β : SiteSectionMultimap LF H ↦ e₃.symm
    (P.map (adj.unit.app (∏ᶜ F)) ≫ R.map (e₂ (e₁ β)))
  have hT : Function.Bijective T :=
    e₃.symm.bijective.comp
      ((site_inverse_image_underlying_hom_bijective J K u (∏ᶜ F) (Q.obj H)).comp
        (e₂.bijective.comp e₁.bijective))
  have hformula (β : SiteSectionMultimap LF H) (U : C)
      (x : ∀ i, (F i).obj.obj (Opposite.op U)) :
      (T β).app U x = β.app (u.obj U) (fun i ↦
        (adj.unit.app (F i)).hom.app (Opposite.op U) (x i)) := by
    change β.app (u.obj U) (productSections LF (u.obj U)
      ((c.hom.hom.app (Opposite.op (u.obj U)))
        ((adj.unit.app (∏ᶜ F)).hom.app (Opposite.op U)
          ((productSections F U).symm x)))) = _
    congr 1
    funext i
    rw [productSections_apply]
    have hc := congrArg (fun g ↦ g.hom.app (Opposite.op (u.obj U)))
      (piComparison_comp_π La F i)
    have hcx := ConcreteCategory.congr_hom hc
      ((adj.unit.app (∏ᶜ F)).hom.app (Opposite.op U) ((productSections F U).symm x))
    change (Pi.π LF i).hom.app (Opposite.op (u.obj U))
      (c.hom.hom.app (Opposite.op (u.obj U)) _) =
        (La.map (Pi.π F i)).hom.app (Opposite.op (u.obj U)) _ at hcx
    rw [hcx]
    have hη := congrArg (fun g ↦ g.hom.app (Opposite.op U))
      (adj.unit.naturality (Pi.π F i))
    have hηx := ConcreteCategory.congr_hom hη ((productSections F U).symm x)
    change (adj.unit.app (F i)).hom.app (Opposite.op U)
      ((Pi.π F i).hom.app (Opposite.op U) ((productSections F U).symm x)) =
        (La.map (Pi.π F i)).hom.app (Opposite.op (u.obj U)) _ at hηx
    have hx : (Pi.π F i).hom.app (Opposite.op U)
        ((productSections F U).symm x) = x i := by
      rw [← productSections_apply, Equiv.apply_symm_apply]
    exact hηx.symm.trans (congrArg ((adj.unit.app (F i)).hom.app (Opposite.op U)) hx)
  obtain ⟨β, hβ⟩ := hT.surjective b
  refine ⟨β, ?_, ?_⟩
  · intro U x
    rw [← hβ]
    exact (hformula β U x).symm
  · intro γ hγ
    apply hT.injective
    rw [hβ]
    apply sectionMultimap_ext
    intro U x
    exact (hformula γ U x).trans (hγ U x)

end CategoryTheory
