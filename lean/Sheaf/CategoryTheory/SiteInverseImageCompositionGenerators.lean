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
  sorry

end CategoryTheory
