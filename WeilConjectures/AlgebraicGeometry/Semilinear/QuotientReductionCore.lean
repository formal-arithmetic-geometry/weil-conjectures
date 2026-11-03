/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import Mathlib.CategoryTheory.Functor.OfSequence
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement

/-! # Ordinary quotient reduction on the sequence site

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 0G7E, 06YY, 07A2 and 06YP;
whole-system refinement extracted from the primitive counit comparison
(blueprint: def-pur-quotient-reduction-core).

All systems are actual module sheaves on the vertical sequence site. Scalar extension
is the recorded sheafified extension, and tensor is the recorded direct-sum total tensor.

## Main definitions

- `quotientConstantRing`, `quotientConstant`: actual constant ring and module systems.
- `quotientRingMap`: the compatible coefficient maps as one sequence-site ring map.
- `quotientReduction`: the cochain functor of ordinary extension of constant systems.
- `quotientTensor`: direct-sum total tensor of two reductions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace WeilConjectures.SemilinearSections
attribute [local irreducible] hasDerived SheafOfModules.monoidalCategory evaluation

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)

variable [small : EssentiallySmall.{max c v r} C]

/-- Pull the ring to the sequence site by the projection; horizontal maps are identities.
Source: Zheng 4.1 (blueprint: lem-pur-quotient-system-flat-models). -/
def quotientConstantRing (R : Sheaf J CommRingCat.{max c v r}) :
    Sheaf (coefficientSequenceTopology J) CommRingCat.{max c v r} :=
  ((CategoryTheory.Prod.snd ℕ C).sheafPushforwardContinuous CommRingCat.{max c v r}
    (coefficientSequenceTopology J) J).obj R

/-- The identity ring map identifies projection precomposition with the constant module
system. Source: Zheng 4.1 (blueprint: lem-pur-quotient-system-flat-models).
Proof: forgetting commutativity and precomposing the projection commute on objects and
maps. The identity section maps therefore give the asserted equality. -/
theorem quotientConstantRing_forget (R : Sheaf J CommRingCat.{max c v r}) :
    ring.{c, v, max c v r} (coefficientSequenceTopology J) (quotientConstantRing.{c, v, r} J R) =
      ((CategoryTheory.Prod.snd ℕ C).sheafPushforwardContinuous RingCat.{max c v r}
        (coefficientSequenceTopology J) J).obj (ring.{c, v, max c v r} J R) := by
  apply ObjectProperty.FullSubcategory.ext
  rfl

/-- The constant system functor has the original modules as every component and identity
horizontal maps. Source: Zheng 4.1 (blueprint: lem-pur-quotient-system-flat-models). -/
def quotientConstant (R : Sheaf J CommRingCat.{max c v r}) :
    Mod.{c, v, max c v r} J R ⥤ Mod.{c, v, max c v r} (coefficientSequenceTopology J)
      (quotientConstantRing.{c, v, r} J R) :=
  SheafOfModules.pushforward (F := CategoryTheory.Prod.snd ℕ C)
    (eqToHom (quotientConstantRing_forget.{c, v, r} J R))

variable (R : Sheaf J CommRingCat.{max c v r})
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (α : ∀ n : ℕ, R ⟶ B n)
  (hα : ∀ n : ℕ, α (n + 1) ≫ τ n = α n)

include hα in
/-- Compatibility of the given algebra maps on the actual sequence presheaves.
Source: Zheng 4.1; Stacks 03EK (blueprint: lem-pur-quotient-system-flat-models).
Proof: iterate hα to all horizontal arrows. Naturality of α_n handles vertical arrows;
the two equations together give naturality on their product. -/
theorem quotientRingMap_naturality {X Y : (ℕ × C)ᵒᵖ} (f : X ⟶ Y) :
    (quotientConstantRing.{c, v, r} J R).obj.map f ≫ (α Y.unop.1).hom.app (op Y.unop.2) =
      (α X.unop.1).hom.app (op X.unop.2) ≫ (systemRing.{c, v, max c v r} J B τ).obj.map f := by
  let cmp : (Functor.const ℕᵒᵖ).obj R ⟶ rings J B τ :=
    NatTrans.ofOpSequence α (by
      intro n
      change 𝟙 R ≫ α n = α (n + 1) ≫ _
      rw [Category.id_comp]
      simpa only [rings, Functor.ofOpSequence_map_homOfLE_succ] using (hα n).symm)
  have h := cmp.naturality (f.unop.1).op
  have hv := (α Y.unop.1).hom.naturality (f.unop.2).op
  change R.obj.map (f.unop.2).op ≫ (α Y.unop.1).hom.app (op Y.unop.2) = _
  rw [hv]
  change _ = (α X.unop.1).hom.app (op X.unop.2) ≫
    ((rings J B τ).map (f.unop.1).op).hom.app (op X.unop.2) ≫
      (B Y.unop.1).obj.map (f.unop.2).op
  change α Y.unop.1 = α X.unop.1 ≫ (rings J B τ).map (f.unop.1).op at h
  have hh := congrArg (fun a ↦ a.hom.app (op X.unop.2)) h
  change (α Y.unop.1).hom.app (op X.unop.2) =
    (α X.unop.1).hom.app (op X.unop.2) ≫
      ((rings J B τ).map (f.unop.1).op).hom.app (op X.unop.2) at hh
  simpa only [Functor.const_obj_map, NatTrans.ofOpSequence_app, Category.id_comp,
    NatTrans.comp_app, Category.assoc] using
    congrArg (fun a ↦ a ≫ (B Y.unop.1).obj.map (f.unop.2).op) hh

/-- The supplied compatible maps R → B_n, as one map of ring sheaves on the sequence site.
Source: Zheng 4.1 (blueprint: lem-pur-quotient-system-flat-models). -/
def quotientRingMap : quotientConstantRing.{c, v, r} J R ⟶ systemRing.{c, v, max c v r} J B τ :=
  ⟨{ app := fun X ↦ (α X.unop.1).hom.app (op X.unop.2)
     naturality := fun _ _ f ↦ quotientRingMap_naturality.{c, v, r} J R B τ α hα f }⟩

end WeilConjectures.SemilinearSections
