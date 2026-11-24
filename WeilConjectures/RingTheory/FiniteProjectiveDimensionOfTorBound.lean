/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.Algebra.FlatTorIdealCriterion
import WeilConjectures.Algebra.TorDimensionShiftFree

/-! # Projective dimension from a Tor bound for finite modules

A finite module over a Noetherian ring whose Tor groups vanish above some bound has
projective dimension at most that bound.

## References

* Stacks Project, Tags 00M5 and 058R, dimension shifting in Tag 00S2.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- A finite module over a Noetherian ring has projective dimension bounded by its Tor bound. -/
theorem finite_hasProjectiveDimensionLE_of_tor_bound
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (d : ℕ)
    (hTor : ∀ N : ModuleCat.{u} R, ∀ i : ℕ, d < i →
      IsZero (((Tor' (ModuleCat.{u} R) i).obj M).obj N)) :
    HasProjectiveDimensionLE M d := by
  induction d generalizing M with
  | zero =>
    have : Module.Flat R M := (flat_iff_tor_one_quotient_ideal R M).mpr
      (fun I ↦ hTor (ModuleCat.of R (R ⧸ I)) 1 (by omega))
    have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
    have : Module.Projective R M := Module.Flat.projective_of_finitePresentation
    have : Projective M := (IsProjective.iff_projective M).mp inferInstance
    exact (projective_iff_hasProjectiveDimensionLE_zero M).mp inferInstance
  | succ d ih =>
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
    let S := f.shortComplexKer
    have hS := LinearMap.shortExact_shortComplexKer hf
    have hK : ∀ N : ModuleCat.{u} R, ∀ i : ℕ, d < i →
        IsZero (((Tor' (ModuleCat.{u} R) i).obj S.X₁).obj N) := by
      intro N i hi
      obtain ⟨e⟩ := (tor_dimension_shift_free S hS N).1 i (by omega)
      exact (hTor N (i + 1) (by omega)).of_iso e.symm
    have hpd := ih S.X₁ hK
    exact (hS.hasProjectiveDimensionLT_X₃_iff d inferInstance).mpr hpd

end ModuleCat
