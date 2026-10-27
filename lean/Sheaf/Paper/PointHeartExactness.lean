/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R7
-/
module

public import Sheaf.Paper.PointHeartFiniteStageData
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Abelian.ShortExact

/-! # Exactness from the essential image of a point-heart functor

Source: BBD, Theorem 1.3.6; the universal-property argument in step 7 of
lem-zl-point-heart-finite-stage (blueprint: lem-zl-point-heart-exactness-from-image).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures

/-- A fully faithful additive functor with exactly the finite-dimensional essential
image has all the exactness properties required of the point-heart equivalence.
Source: BBD, Theorem 1.3.6; step 7 of lem-zl-point-heart-finite-stage
(blueprint: lem-zl-point-heart-exactness-from-image).

Proof: factor through finitely generated modules. Full faithfulness and the stated
essential image make this factor an equivalence. Finite-dimensional modules form an
abelian category whose inclusion preserves finite limits and colimits. Transport the
abelian structure to the source. The original functor therefore preserves finite limits
and colimits, and full faithfulness reflects them. A zero object is characterized by its
unique incoming and outgoing maps; short exactness is reflected by a faithful functor
between abelian categories and preserved by an exact functor. -/
theorem zlPointHeartExact_of_essentialImage
    {C : Type v} [Category.{w} C] [Preadditive C]
    (F : Type u) [Field F] (ω : C ⥤ ModuleCat.{u} F)
    (hfull : ω.Full) (hfaithful : ω.Faithful) (hadd : ω.Additive)
    (hfinite : ∀ X, FiniteDimensional F (ω.obj X))
    (himage : ∀ V : ModuleCat.{u} F, FiniteDimensional F V →
      ∃ X, Nonempty (ω.obj X ≅ V)) : ZlPointHeartExact F ω := by
  let := hfull
  let := hfaithful
  let := hadd
  let G : C ⥤ FGModuleCat.{u} F := (ModuleCat.isFG F).lift ω hfinite
  let : G.EssSurj := ⟨fun V ↦ by
    obtain ⟨X, ⟨e⟩⟩ := himage V.obj V.property
    exact ⟨X, ⟨(ModuleCat.isFG F).fullyFaithfulι.preimageIso e⟩⟩⟩
  let : G.IsEquivalence := {}
  let : HasFiniteLimits C :=
    ⟨fun _ _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence G⟩
  let : Abelian C := abelianOfEquivalence G
  have : PreservesFiniteLimits ω := by
    change PreservesFiniteLimits (G ⋙ forget₂ (FGModuleCat.{u} F) (ModuleCat.{u} F))
    exact comp_preservesFiniteLimits G (forget₂ (FGModuleCat.{u} F) (ModuleCat.{u} F))
  have : PreservesFiniteColimits ω := by
    change PreservesFiniteColimits (G ⋙ forget₂ (FGModuleCat.{u} F) (ModuleCat.{u} F))
    exact comp_preservesFiniteColimits G (forget₂ (FGModuleCat.{u} F) (ModuleCat.{u} F))
  refine ⟨hfull, hfaithful, hadd, hfinite, himage, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_⟩
  · intro X
    exact ⟨IsZero.of_full_of_faithful_of_isZero ω X, fun h ↦ ω.map_isZero h⟩
  · intro _ S
    exact CategoryTheory.ShortExact.shortExact_map_iff ω

end WeilConjectures
