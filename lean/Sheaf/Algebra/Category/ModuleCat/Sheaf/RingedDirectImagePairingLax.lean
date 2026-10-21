/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal

/-! # Normalized lax tensor pairing for ringed direct image

Source: Stacks Project, Modules on Sites, Tags 03D6 and 03EK; lax coherence and
regular-unit uniqueness extracted from their sectionwise constructions.
(blueprint: lem-pd-ringed-direct-image-pairing-lax)

The tensor, associators and unitors are the existing localization construction.
The pushforward is Mathlib's precomposition with restriction of scalars.
-/

@[expose] public section

universe uC vC uD vD w

open CategoryTheory MonoidalCategory

namespace SheafOfModules

set_option autoImplicit false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (v : C ⥤ D) [v.IsContinuous J K]
  (R : Sheaf J CommRingCat.{w}) (S : Sheaf K CommRingCat.{w})
  (c : (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R ⟶
    (v.sheafPushforwardContinuous RingCat.{w} J K).obj
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S))

/-- The local pure-tensor normalization for a lax structure on ringed direct image.
This is only a predicate on the existing tensor and pushforward, with no additional data.
Source: Stacks Project, Modules on Sites, Tags 03D6 and 03EK
(blueprint: lem-pd-ringed-direct-image-pairing-lax). -/
def RingedPushforwardPureTensor
    (L : (pushforward.{w} c).LaxMonoidal) : Prop :=
  ∀ (M N : CategoryTheory.ringedSiteModules.{w}
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (U : Cᵒᵖ) (x : M.val.obj (v.op.obj U)) (y : N.val.obj (v.op.obj U)),
    (@Functor.LaxMonoidal.μ _ _ _ _ _ _ (pushforward.{w} c) L M N).val.app U
      ((tensorObjIsoSheafification ((pushforward c).obj M) ((pushforward c).obj N)).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)).unit.app
            (((pushforward c).obj M).val ⊗ ((pushforward c).obj N).val)).app U
              (x ⊗ₜ[R.obj.obj U] y))) =
      (tensorObjIsoSheafification M N).inv.val.app (v.op.obj U)
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S).obj)).unit.app
            (M.val ⊗ N.val)).app (v.op.obj U) (x ⊗ₜ[S.obj.obj (v.op.obj U)] y))

/-- The direct image has exactly one lax structure with the prescribed local pure tensors;
its unit is the given coefficient map. Uniqueness assumes only the tensor normalization.
Source: Stacks Project, Modules on Sites, Tags 03D6 and 03EK; agent extraction of
coherence and regular-unit uniqueness
(blueprint: lem-pd-ringed-direct-image-pairing-lax).

Proof:
1. Restrict scalars along `c` in the precomposition functor. Naturality and the ring-map
   equations give the module axioms and linear restrictions. The map `e_U(r) = c_U(r)`
   is a module-sheaf morphism [def-weil-sheaf-of-modules-category].
2. The target pure tensor gives a restriction-compatible R-bilinear pairing. The
   sheaf-tensor bilinear universal property [lem-pc-sites-sheaf-tensor-bilinear-universal]
   gives a unique tensorator with the required formula [def-pur-sheaf-tensor-product].
3. Both naturality composites send a pure tensor to the tensor of the two images;
   injectivity in that universal property proves naturality in both variables.
4. The left and right unit composites send `r ⊗ x` and `x ⊗ r` to `c_U(r) x`.
   The canonical unitors [lem-pc-sheaf-modules-tensor-closed] have the same values,
   so the bilinear universal property gives both unit identities.
5. Curry maps from a triple tensor using the symmetry and tensor-Hom adjunction
   [lem-pc-sheaf-modules-tensor-closed]. The bilinear universal property and evaluation
   of internal Hom on every further restriction [def-pur-sheaf-hom] test equality on
   triples of local sections. Both associativity composites send `(x ⊗ y) ⊗ z` to
   `x ⊗ (y ⊗ z)`, hence agree.
6. Any other normalized tensorator is equal by the bilinear universal property.
   Its left unit identity at the regular S-module on `1_R ⊗ 1_S` forces `e'_U(1)=1`.
   R-linearity then forces `e'_U(r)=c_U(r)`, so the units and whole lax structures agree.
-/
theorem exists_unique_ringedPushforward_laxMonoidal :
    ∃ L : (pushforward.{w} c).LaxMonoidal,
      RingedPushforwardPureTensor v R S c L ∧
      (∀ (U : Cᵒᵖ) (r : R.obj.obj U),
        (@Functor.LaxMonoidal.ε _ _ _ _ _ _ (pushforward.{w} c) L).val.app U r =
          c.hom.app U r) ∧
      ∀ L' : (pushforward.{w} c).LaxMonoidal,
        RingedPushforwardPureTensor v R S c L' → L' = L := by
  sorry

end SheafOfModules
