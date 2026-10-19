/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q93
-/
module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Composition of inverse images on canonical generators

Source: Stacks Project, Sites, Tags 00VE, 00WX and 03CB
(blueprint: lem-trf-site-inverse-image-composition-generators).
-/

@[expose] public section

universe u w t a

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

section Coefficients

variable {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (L : GrothendieckTopology E) (v : C ⥤ D) (u : D ⥤ E)
  (A : Type a) [Category.{t} A] [HasColimitsOfSize.{u, u} A]
  [v.IsContinuous J K] [u.IsContinuous K L]
  [HasWeakSheafify K A] [HasWeakSheafify L A]

/-- The colimit coprojection followed by sheafification, expressed as the identity-index
coprojection (the adjunction unit) followed by restriction along `φ`.
Source: Stacks Project, Sites, Tags 00VE and 00WX. This uses the constructed inverse image,
not a separately chosen left adjoint.
(blueprint: lem-trf-site-inverse-image-composition-generators). -/
noncomputable def siteInverseImageGenerator (F : Sheaf J A) (W : C) (V : D)
    (φ : V ⟶ v.obj W) :
    F.obj.obj (op W) ⟶ ((sheafPullback v A J K).obj F).obj.obj (op V) :=
  ((sheafAdjunctionContinuous v A J K).unit.app F).hom.app (op W) ≫
    ((sheafPullback v A J K).obj F).obj.map φ.op

/-- The nested canonical generator in two successive constructed inverse images.
Source: Stacks Project, Sites, Tags 00VE, 00WX and 03CB.
(blueprint: lem-trf-site-inverse-image-composition-generators). -/
noncomputable def siteInverseImageNestedGenerator (F : Sheaf J A)
    (U : E) (V : D) (W : C) (φ : U ⟶ u.obj V) (ψ : V ⟶ v.obj W) :
    F.obj.obj (op W) ⟶
      ((sheafPullback u A K L).obj ((sheafPullback v A J K).obj F)).obj.obj (op U) :=
  siteInverseImageGenerator J K v A F W V ψ ≫
    siteInverseImageGenerator K L u A ((sheafPullback v A J K).obj F) V U φ

/-- The statement of composition compatibility for a specified coefficient category.
The equations are equations of maps out of `F(W)`: for sets and abelian groups these
are exactly equality on every element, including the equality-detection premise.
The last two clauses give naturality of the nested generators in the input sheaf and
compatibility with restriction. The comparison itself is a natural isomorphism of
sheaf functors, so its naturality in both variables is part of its type.
Source: Stacks Project, Sites, Tags 00VE, 00WX and 03CB.
(blueprint: lem-trf-site-inverse-image-composition-generators). -/
def SiteInverseImageCompositionGenerators : Prop :=
  letI := Functor.isContinuous_comp v u J K L
  ∃ κ : sheafPullback v A J K ⋙ sheafPullback u A K L ≅
      sheafPullback (v ⋙ u) A J L,
    (∀ F : Sheaf J A,
      ((sheafAdjunctionContinuous v A J K).unit.app F) ≫
        (v.sheafPushforwardContinuous A J K).map
          ((sheafAdjunctionContinuous u A K L).unit.app
            ((sheafPullback v A J K).obj F)) ≫
        (v.sheafPushforwardContinuous A J K).map
          ((u.sheafPushforwardContinuous A K L).map (κ.hom.app F)) =
      (sheafAdjunctionContinuous (v ⋙ u) A J L).unit.app F) ∧
    (∀ κ' : sheafPullback v A J K ⋙ sheafPullback u A K L ≅
        sheafPullback (v ⋙ u) A J L,
      (∀ F : Sheaf J A,
        ((sheafAdjunctionContinuous v A J K).unit.app F) ≫
          (v.sheafPushforwardContinuous A J K).map
            ((sheafAdjunctionContinuous u A K L).unit.app
              ((sheafPullback v A J K).obj F)) ≫
          (v.sheafPushforwardContinuous A J K).map
            ((u.sheafPushforwardContinuous A K L).map (κ'.hom.app F)) =
        (sheafAdjunctionContinuous (v ⋙ u) A J L).unit.app F) → κ' = κ) ∧
    (∀ (F : Sheaf J A) (U : E) (V : D) (W : C)
        (φ : U ⟶ u.obj V) (ψ : V ⟶ v.obj W),
      siteInverseImageNestedGenerator J K L v u A F U V W φ ψ ≫
        (κ.hom.app F).hom.app (op U) =
      siteInverseImageGenerator J L (v ⋙ u) A F W U (φ ≫ u.map ψ)) ∧
    (∀ (F : Sheaf J A) (H : Sheaf L A)
        (α β : (sheafPullback u A K L).obj ((sheafPullback v A J K).obj F) ⟶ H),
      (∀ (U : E) (V : D) (W : C) (φ : U ⟶ u.obj V) (ψ : V ⟶ v.obj W),
        siteInverseImageNestedGenerator J K L v u A F U V W φ ψ ≫ α.hom.app (op U) =
        siteInverseImageNestedGenerator J K L v u A F U V W φ ψ ≫ β.hom.app (op U)) →
      α = β) ∧
    (∀ (F F' : Sheaf J A) (f : F ⟶ F') (U : E) (V : D) (W : C)
        (φ : U ⟶ u.obj V) (ψ : V ⟶ v.obj W),
      siteInverseImageNestedGenerator J K L v u A F U V W φ ψ ≫
        ((sheafPullback v A J K ⋙ sheafPullback u A K L).map f).hom.app (op U) =
      f.hom.app (op W) ≫ siteInverseImageNestedGenerator J K L v u A F' U V W φ ψ) ∧
    (∀ (F : Sheaf J A) (U U' : E) (r : U' ⟶ U) (V : D) (W : C)
        (φ : U ⟶ u.obj V) (ψ : V ⟶ v.obj W),
      siteInverseImageNestedGenerator J K L v u A F U V W φ ψ ≫
        ((sheafPullback u A K L).obj ((sheafPullback v A J K).obj F)).obj.map r.op =
      siteInverseImageNestedGenerator J K L v u A F U' V W (r ≫ φ) ψ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem nested_generator_eq (F : Sheaf J A)
    (U : E) (V : D) (W : C) (φ : U ⟶ u.obj V) (ψ : V ⟶ v.obj W) :
    siteInverseImageNestedGenerator J K L v u A F U V W φ ψ =
      ((sheafAdjunctionContinuous v A J K).unit.app F).hom.app (op W) ≫
        ((sheafAdjunctionContinuous u A K L).unit.app
          ((sheafPullback v A J K).obj F)).hom.app (op (v.obj W)) ≫
        ((sheafPullback u A K L).obj ((sheafPullback v A J K).obj F)).obj.map
          (φ ≫ u.map ψ).op := by
  let P := (sheafPullback v A J K).obj F
  let Q := (sheafPullback u A K L).obj P
  let η := (sheafAdjunctionContinuous u A K L).unit.app P
  let a : F.obj.obj (op W) ⟶ P.obj.obj (op (v.obj W)) :=
    ((sheafAdjunctionContinuous v A J K).unit.app F).hom.app (op W)
  have hn : P.obj.map ψ.op ≫ η.hom.app (op V) =
      η.hom.app (op (v.obj W)) ≫ Q.obj.map (u.map ψ).op :=
    η.hom.naturality ψ.op
  change (a ≫ P.obj.map ψ.op) ≫ (η.hom.app (op V) ≫ Q.obj.map φ.op) =
    a ≫ η.hom.app (op (v.obj W)) ≫ Q.obj.map (φ ≫ u.map ψ).op
  calc
    _ = a ≫ (P.obj.map ψ.op ≫ η.hom.app (op V)) ≫ Q.obj.map φ.op := by
      simp only [Category.assoc]
    _ = a ≫ (η.hom.app (op (v.obj W)) ≫ Q.obj.map (u.map ψ).op) ≫
        Q.obj.map φ.op := congrArg (fun f ↦ a ≫ f ≫ Q.obj.map φ.op) hn
    _ = _ := by simp only [op_comp, Functor.map_comp, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem composition_generators :
    SiteInverseImageCompositionGenerators J K L v u A := by
  let := Functor.isContinuous_comp v u J K L
  let adj := (sheafAdjunctionContinuous v A J K).comp
    (sheafAdjunctionContinuous u A K L)
  let adj' : sheafPullback (v ⋙ u) A J L ⊣
      u.sheafPushforwardContinuous A K L ⋙ v.sheafPushforwardContinuous A J K :=
    sheafAdjunctionContinuous (v ⋙ u) A J L
  let κ := adj.leftAdjointUniq adj'
  refine ⟨κ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro F
    simpa only [adj, adj', κ, Adjunction.comp_unit_app, Functor.comp_map, Category.assoc] using
      adj.unit_leftAdjointUniq_hom_app adj' F
  · intro κ' hκ'
    apply Iso.ext
    apply NatTrans.ext
    funext F
    apply (adj.homEquiv F _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    simpa only [adj, adj', κ, Adjunction.comp_unit_app, Functor.comp_map, Category.assoc] using
      (hκ' F).trans (by
        simpa only [adj, adj', κ, Adjunction.comp_unit_app, Functor.comp_map, Category.assoc] using
          (adj.unit_leftAdjointUniq_hom_app adj' F).symm)
  · intro F U V W φ ψ
    let P := (sheafPullback v A J K).obj F
    let Q := (sheafPullback u A K L).obj P
    let R := (sheafPullback (v ⋙ u) A J L).obj F
    let a : F.obj.obj (op W) ⟶ Q.obj.obj (op ((v ⋙ u).obj W)) :=
      ((sheafAdjunctionContinuous v A J K).unit.app F).hom.app (op W) ≫
        ((sheafAdjunctionContinuous u A K L).unit.app P).hom.app (op (v.obj W))
    have hκ : a ≫ (κ.hom.app F).hom.app (op ((v ⋙ u).obj W)) =
        ((sheafAdjunctionContinuous (v ⋙ u) A J L).unit.app F).hom.app (op W) := by
      have hh := congrArg (fun f ↦ f.hom.app (op W))
        (adj.unit_leftAdjointUniq_hom_app adj' F)
      simpa only [a, P, Q, adj, adj', κ, Adjunction.comp_unit_app,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Functor.comp_map,
        Functor.sheafPushforwardContinuous_map_hom_app,
        Functor.comp_obj, Functor.id_obj, Category.assoc] using hh
    have hn : Q.obj.map (φ ≫ u.map ψ).op ≫ (κ.hom.app F).hom.app (op U) =
        (κ.hom.app F).hom.app (op ((v ⋙ u).obj W)) ≫
          R.obj.map (φ ≫ u.map ψ).op :=
      (κ.hom.app F).hom.naturality (φ ≫ u.map ψ).op
    rw [nested_generator_eq]
    dsimp only [siteInverseImageGenerator]
    simp only [← Category.assoc] at ⊢
    change (a ≫ Q.obj.map (φ ≫ u.map ψ).op) ≫ (κ.hom.app F).hom.app (op U) =
      ((sheafAdjunctionContinuous (v ⋙ u) A J L).unit.app F).hom.app (op W) ≫
        R.obj.map (φ ≫ u.map ψ).op
    calc
      _ = a ≫ (Q.obj.map (φ ≫ u.map ψ).op ≫ (κ.hom.app F).hom.app (op U)) :=
        Category.assoc _ _ _
      _ = a ≫ ((κ.hom.app F).hom.app (op ((v ⋙ u).obj W)) ≫
          R.obj.map (φ ≫ u.map ψ).op) := congrArg (fun f ↦ a ≫ f) hn
      _ = _ := by rw [← Category.assoc, hκ]
  · intro F H α β h
    apply (adj.homEquiv F H).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    have hh := h ((v ⋙ u).obj W.unop) (v.obj W.unop) W.unop (𝟙 _) (𝟙 _)
    dsimp only [siteInverseImageNestedGenerator, siteInverseImageGenerator] at hh
    erw [Functor.map_id, Functor.map_id, Category.comp_id, Category.comp_id] at hh
    simpa only [adj, Adjunction.comp_unit_app,
      ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Functor.comp_map,
      Functor.sheafPushforwardContinuous_map_hom_app,
        Functor.comp_obj, Functor.id_obj, Category.assoc] using hh
  · intro F F' f U V W φ ψ
    let T := sheafPullback v A J K ⋙ sheafPullback u A K L
    let Q := T.obj F
    let Q' := T.obj F'
    let g := T.map f
    let a : F.obj.obj (op W) ⟶ Q.obj.obj (op (u.obj (v.obj W))) :=
      ((sheafAdjunctionContinuous v A J K).unit.app F).hom.app (op W) ≫
        ((sheafAdjunctionContinuous u A K L).unit.app
          ((sheafPullback v A J K).obj F)).hom.app (op (v.obj W))
    let a' : F'.obj.obj (op W) ⟶ Q'.obj.obj (op (u.obj (v.obj W))) :=
      ((sheafAdjunctionContinuous v A J K).unit.app F').hom.app (op W) ≫
        ((sheafAdjunctionContinuous u A K L).unit.app
          ((sheafPullback v A J K).obj F')).hom.app (op (v.obj W))
    have hη : a ≫ g.hom.app (op (u.obj (v.obj W))) = f.hom.app (op W) ≫ a' := by
      have hh := congrArg (fun h ↦ h.hom.app (op W)) (adj.unit.naturality f)
      simpa only [a, a', Q, Q', g, T, adj, Adjunction.comp_unit_app,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Functor.comp_map,
        Functor.sheafPushforwardContinuous_map_hom_app,
        Functor.comp_obj, Functor.id_obj, Functor.id_map, Category.assoc] using
        hh.symm
    have hn : Q.obj.map (φ ≫ u.map ψ).op ≫ g.hom.app (op U) =
        g.hom.app (op (u.obj (v.obj W))) ≫ Q'.obj.map (φ ≫ u.map ψ).op :=
      g.hom.naturality (φ ≫ u.map ψ).op
    rw [nested_generator_eq, nested_generator_eq]
    simp only [← Category.assoc] at ⊢
    change (a ≫ Q.obj.map (φ ≫ u.map ψ).op) ≫ g.hom.app (op U) =
      ((f.hom.app (op W) ≫
        ((sheafAdjunctionContinuous v A J K).unit.app F').hom.app (op W)) ≫
        ((sheafAdjunctionContinuous u A K L).unit.app
          ((sheafPullback v A J K).obj F')).hom.app (op (v.obj W))) ≫
          Q'.obj.map (φ ≫ u.map ψ).op
    rw [Category.assoc (f.hom.app (op W))]
    change _ = (f.hom.app (op W) ≫ a') ≫ Q'.obj.map (φ ≫ u.map ψ).op
    calc
      _ = a ≫ (Q.obj.map (φ ≫ u.map ψ).op ≫ g.hom.app (op U)) :=
        Category.assoc _ _ _
      _ = a ≫ (g.hom.app (op (u.obj (v.obj W))) ≫
          Q'.obj.map (φ ≫ u.map ψ).op) := congrArg (fun h ↦ a ≫ h) hn
      _ = _ := by rw [← Category.assoc, hη]
  · intro F U U' r V W φ ψ
    simp [siteInverseImageNestedGenerator, siteInverseImageGenerator,
      ← Functor.map_comp, ← op_comp]

end Coefficients

/-- The preceding composition statement for the two coefficient categories of the node.
The only local instance is Mathlib's restriction of preservation of filtered colimits to
the universe of the small sites. It supplies abelian sheafification without an extra
hypothesis or any equality between the site and coefficient universes.
Source: Stacks Project, Sites, Tags 00WX and 03CB.
(blueprint: lem-trf-site-inverse-image-composition-generators). -/
def SiteInverseImageCompositionGeneratorsForSetsAndAbelianGroups
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E) (v : C ⥤ D) (u : D ⥤ E)
    [v.IsContinuous J K] [u.IsContinuous K L] : Prop :=
  letI : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{max u w}) :=
    preservesFilteredColimitsOfSize_shrink.{u, w, u, w} _
  SiteInverseImageCompositionGenerators J K L v u (Type (max u w)) ∧
    SiteInverseImageCompositionGenerators J K L v u AddCommGrpCat.{max u w}

/-- Successive inverse images of set sheaves and abelian sheaves have a unique
unit-compatible comparison with the inverse image for the composite. It sends each nested
colimit generator to the generator indexed by the composite arrow; the nested generators
detect equality of sheaf morphisms, naturally in the sheaf and under restrictions.
Source: Stacks Project, Sites, Tags 03CB, 00VE and 00WX, and Categories, Tag 0B65.
(blueprint: lem-trf-site-inverse-image-composition-generators).

Proof: (1) Precomposition preserves sheaves by continuity, and precomposition by the composite
is the composite of the two direct images, on objects and maps. Use the constructed
sheafPullback and sheafAdjunctionContinuous for all three functors; these are left Kan
extension followed by sheafification, with the prescribed colimit coprojections.
(2) Compose the two adjunctions using Adjunction.comp (def-weil-pbc-composite-adjunction).
Its unit is the first unit followed by the direct image of the second. Apply the conjugate
isomorphism and its unit equation (lem-weil-pbc-conjugate-iso-unit-equation) to the identity
comparison of direct images. This gives the unique unit-compatible natural isomorphism.
(3) Evaluate the unit equation on identity-index generators. For general arrows ψ and φ,
restrict this equality along ψ and then φ, using naturality of the units, the comparison,
and the colimit coprojections. This gives precisely the displayed composite-arrow formula,
after the sheafification unit; it requires no single-representative description of sections.
(4) Transpose two maps through the composite adjunction. On each x in F(W), the composite
unit is the identity-index nested generator. The assumed generator equalities therefore
identify the adjuncts componentwise; injectivity of the hom equivalence, equivalently
lem-weil-pbc-adjunct-counit-identity, identifies the original maps.
(5) Naturality of both units and of the comparison proves functoriality in F. Functoriality
of restrictions gives compatibility with U' → U. These arguments apply to colimits in sets
and to colimits in abelian groups, without asserting every section is one generator. -/
theorem site_inverse_image_composition_generators
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E) (v : C ⥤ D) (u : D ⥤ E)
    [v.IsContinuous J K] [u.IsContinuous K L] :
    SiteInverseImageCompositionGeneratorsForSetsAndAbelianGroups.{u, w} J K L v u := by
  let : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{max u w}) :=
    preservesFilteredColimitsOfSize_shrink.{u, w, u, w} _
  exact ⟨composition_generators J K L v u (Type (max u w)),
    composition_generators J K L v u AddCommGrpCat.{max u w}⟩

end CategoryTheory
