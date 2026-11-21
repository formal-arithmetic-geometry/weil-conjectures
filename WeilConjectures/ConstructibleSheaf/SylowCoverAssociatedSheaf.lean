/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.ConstructibleSheaf.SylowCoverStalkData
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits

/-!
# A Sylow cover and its associated-sheaf functor

Source: Stacks Project, Tags 0A3R, 0DV5 and 0DV6.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

/-- The geometric part of the Sylow reduction, without constructing any filtration.

Source: Stacks Project, `etale-cohomology.tex`, Lemma 0A3R, first part of the proof. -/
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_sylow_cover_associated_sheaf
    {U : Scheme.{u}} [ConnectedSpace U] (ℓ : ℕ) [Fact ℓ.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    [IsFiniteLocallyConstantSheaf G] :
    ∃ (V : Scheme.{u}) (v : V ⟶ U) (_ : IsFinite v) (_ : Etale v) (_ : ConnectedSpace V)
      (d : ℕ), ¬ ℓ ∣ d ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
        Nat.card (v.GeometricFiber s) = d) ∧
      ∃ (P : Type u) (_ : Group P) (_ : Finite P), IsPGroup ℓ P ∧
        ∃ (M : Rep.{u + 1} (ZMod ℓ) P) (_ : FiniteDimensional (ZMod ℓ) M.V)
          (T : Rep.{u + 1} (ZMod ℓ) P ⥤
            Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
          (_ : T.Additive) (_ : PreservesFiniteLimits T) (_ : PreservesFiniteColimits T),
          Nonempty (T.obj M ≅ (v)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj G) ∧
          Nonempty (T.obj (Rep.trivial (ZMod ℓ) P (ULift.{u + 1} (ZMod ℓ))) ≅
            (constantSheaf V.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
              (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))) := by
  obtain ⟨V, v, hv, he, hc, d, hd, hf, P, hg, hfin, hp, M, hm, T, ha, hs, eM, e1⟩ :=
    Scheme.IsFiniteLocallyConstantSheaf.exists_sylow_cover_stalk_data ℓ G
  let R : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)) ⥤
      ModuleCat.{u + 1} (ZMod ℓ) := ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv.symm.toRingHom : ZMod ℓ →+* ULift.{u + 1} (ZMod ℓ))
  have : R.IsEquivalence := inferInstance
  have : ReflectsFiniteLimits R := by
    have : ReflectsLimitsOfSize.{0, 0} R := fullyFaithful_reflectsLimits R
    exact ReflectsLimitsOfSize.reflectsFiniteLimits R
  have : ReflectsFiniteColimits R := by
    have : ReflectsColimitsOfSize.{0, 0} R := fullyFaithful_reflectsColimits R
    exact ReflectsColimitsOfSize.reflectsFiniteColimits R
  have hL (x : V) : PreservesFiniteLimits (T ⋙ (V.uliftPointSmallEtale x).sheafFiber
      (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) := by
    obtain ⟨e⟩ := hs x
    let S := (V.uliftPointSmallEtale x).sheafFiber
      (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    have : PreservesFiniteLimits ((T ⋙ S) ⋙ R) :=
      preservesFiniteLimits_of_natIso ((Functor.associator T S R) ≪≫ e).symm
    exact preservesFiniteLimits_of_reflects_of_preserves
      (T ⋙ (V.uliftPointSmallEtale x).sheafFiber
        (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) R
  have hC (x : V) : PreservesFiniteColimits (T ⋙ (V.uliftPointSmallEtale x).sheafFiber
      (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) := by
    obtain ⟨e⟩ := hs x
    let S := (V.uliftPointSmallEtale x).sheafFiber
      (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    have : PreservesFiniteColimits ((T ⋙ S) ⋙ R) :=
      preservesFiniteColimits_of_natIso ((Functor.associator T S R) ≪≫ e).symm
    exact preservesFiniteColimits_of_reflects_of_preserves
      (T ⋙ (V.uliftPointSmallEtale x).sheafFiber
        (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) R
  have hl : PreservesFiniteLimits T := by
    constructor
    intro J _ _
    constructor
    intro K
    apply preservesLimit_of_preserves_limit_cone (limit.isLimit K)
    apply (Scheme.jointlyReflectIsomorphisms_ulift_pointSmallEtale V _).jointlyReflectsLimit
    intro p
    apply Classical.choice
    rcases p with ⟨_, ⟨x⟩⟩
    have := hL x
    exact ⟨isLimitOfPreserves (T ⋙ (V.uliftPointSmallEtale x).sheafFiber
      (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) (limit.isLimit K)⟩
  have hcol : PreservesFiniteColimits T := by
    constructor
    intro J _ _
    constructor
    intro K
    apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K)
    apply (Scheme.jointlyReflectIsomorphisms_ulift_pointSmallEtale V _).jointlyReflectsColimit
    intro p
    apply Classical.choice
    rcases p with ⟨_, ⟨x⟩⟩
    have := hC x
    exact ⟨isColimitOfPreserves (T ⋙ (V.uliftPointSmallEtale x).sheafFiber
      (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
      (colimit.isColimit K)⟩
  exact ⟨V, v, hv, he, hc, d, hd, hf, P, hg, hfin, hp, M, hm, T, ha, hl, hcol, eM, e1⟩

end AlgebraicGeometry
