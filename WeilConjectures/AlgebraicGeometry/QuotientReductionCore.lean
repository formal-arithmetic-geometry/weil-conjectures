/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
import Mathlib.CategoryTheory.Functor.OfSequence
import all WeilConjectures.AlgebraicGeometry.SemilinearDerivedCalculusSupplement

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

/-- The sequence projection pulls sheaves back to constant sequences.
Source: Zheng Construction 4.1; Stacks 0941
(blueprint: lem-pur-quotient-system-flat-models).
Proof: a matching family for a vertical cover glues on its C-coordinate. The unique
amalgamation is unchanged along horizontal arrows, so the precomposition is a sheaf.
This is precisely continuity of the projection for the vertical topology. -/
theorem quotientProjection_continuous :
    (CategoryTheory.Prod.snd ℕ C).IsContinuous (coefficientSequenceTopology J) J := by
  apply Functor.isContinuous_of_coverPreserving
  · constructor
    intro G Z T x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ he
    exact hx
      (Prod.mkHom (homOfLE (Nat.min_le_left Y₁.1 Y₂.1)) f₁)
      (Prod.mkHom (homOfLE (Nat.min_le_right Y₁.1 Y₂.1)) f₂)
      hg₁ hg₂ (by
        apply Prod.hom_ext
        · apply Subsingleton.elim
        · exact he)
  · constructor
    intro X S hS
    apply J.superset_covering _ hS
    intro V f hf
    exact Sieve.image_mem_functorPushforward (CategoryTheory.Prod.snd ℕ C) S hf

/-- The continuity witness for the actual projection, with no chosen inverse image.
Source: Zheng 4.1 (blueprint: lem-pur-quotient-system-flat-models). -/
instance quotientProjectionContinuous :
    (CategoryTheory.Prod.snd ℕ C).IsContinuous (coefficientSequenceTopology J) J :=
  quotientProjection_continuous J

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

/-- Constant sequences are additive and exact.
Source: Zheng 4.1; Stacks 0941 (blueprint: lem-pur-quotient-system-flat-models).
Proof: the functor is identity on every vertical slice. Kernels and sheafified cokernels
are componentwise by lem-coef-semilinear-derived-sections, so it preserves both. -/
theorem quotientConstant_exact (R : Sheaf J CommRingCat.{max c v r}) :
    (quotientConstant.{c, v, r} J R).Additive ∧ PreservesFiniteLimits (quotientConstant.{c, v, r}
      J R) ∧
      PreservesFiniteColimits (quotientConstant.{c, v, r} J R) := by
  have : (CategoryTheory.Prod.snd ℕ C).IsCocontinuous (coefficientSequenceTopology J) J := by
    constructor
    intro X S hS
    exact hS
  exact modulePushforward_exact.{c, v, r, c, v}
    (eqToHom (quotientConstantRing_forget.{c, v, r} J R))

/-- Additivity of the canonical constant system functor.
Source: Zheng 4.1 (blueprint: lem-pur-quotient-system-flat-models). -/
instance quotientConstantAdditive (R : Sheaf J CommRingCat.{max c v r}) :
    (quotientConstant.{c, v, r} J R).Additive := (quotientConstant_exact.{c, v, r} J R).1

/-- Left exactness of the canonical constant system functor.
Source: Zheng 4.1 (blueprint: lem-pur-quotient-system-flat-models). -/
instance quotientConstantLimits (R : Sheaf J CommRingCat.{max c v r}) :
    PreservesFiniteLimits (quotientConstant.{c, v, r} J R) := (quotientConstant_exact.{c, v, r} J
      R).2.1

/-- Right exactness of the canonical constant system functor.
Source: Zheng 4.1 (blueprint: lem-pur-quotient-system-flat-models). -/
instance quotientConstantColimits (R : Sheaf J CommRingCat.{max c v r}) :
    PreservesFiniteColimits (quotientConstant.{c, v, r} J R) := (quotientConstant_exact.{c, v, r}
      J R).2.2

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

/-- Ordinary coherent reduction, using the prescribed sheafified change of rings of the
recorded scalar model. No arbitrary system map enters this construction.
Source: Stacks 03EK, 06YY (blueprint: lem-pur-quotient-system-flat-models). -/
def quotientReduction (S : ScalarData.{c, v, max c v r} (quotientRingMap.{c, v, r} J R B τ α hα)) :
    CochainComplex (Mod.{c, v, max c v r} J R) ℤ ⥤ CochainComplex (Systems.{c, v, max c v r} J B
      τ) ℤ :=
  (quotientConstant.{c, v, r} J R ⋙ S.model.E).mapHomologicalComplex (.up ℤ)

/-- The strict tensor system Z_T is the actual total tensor of the two strict reductions.
Source: Stacks 06YN, 07A4 (blueprint: lem-pur-quotient-system-flat-models). -/
def quotientTensor (S : ScalarData.{c, v, max c v r} (quotientRingMap.{c, v, r} J R B τ α hα)) :=
  ((quotientReduction.{c, v, r} J R B τ α hα S).prod
    (quotientReduction.{c, v, r} J R B τ α hα S)) ⋙
      totalTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ)

end WeilConjectures.SemilinearSections
