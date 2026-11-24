/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.Depth
public import WeilConjectures.Mathlib.Topology.KrullDimension

import WeilConjectures.AlgebraicGeometry.PolynomialChartLocalAlgebra
import WeilConjectures.RingTheory.MiracleFlatness
import WeilConjectures.RingTheory.FlatLocalDepthFormula
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.DepthLeSupportDimension
import WeilConjectures.RingTheory.RingKrullDimLeOfFaithfullyFlatOfIsLocalHom
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Fibre flatness on a quasi-finite polynomial chart

## References

* Stacks Project, Tags 00RE, 00R7, 00RH and 00N8.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

private theorem regular_local_depth_eq (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞)) :
    IsLocalRing.depth (R := R) R = (d : ℕ∞) := by
  classical
  have hu := IsLocalRing.depth_le_supportDim (R := R) R
  rw [Module.supportDim_self_eq_ringKrullDim, hd] at hu
  apply le_antisymm (WithBot.coe_le_coe.mp hu)
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (show (IsLocalRing.maximalIdeal R).FG from
        (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing)
  have hlen : s.toList.length = d := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hd] at h
    have hsd : (IsLocalRing.maximalIdeal R).spanFinrank = d := by exact_mod_cast h
    simpa [hsd] using hcard
  have hrs : IsLocalRing.IsRegularSystemOfParameters s.toList :=
    ⟨by simpa using hspan, by rw [hlen, hd]⟩
  have hreg := (IsRegularLocalRing.isRegular_and_quotients_of_generators R d hd
    s.toList hrs).1
  unfold IsLocalRing.depth Ideal.depth
  split
  · exact le_top
  · apply le_sSup
    exact ⟨s.toList, hreg, fun x hx ↦ hrs.1 ▸ Ideal.subset_span hx, by rw [hlen]⟩

/-- Flatness on a quasi-finite polynomial chart is equivalent to Cohen-Macaulayness
of the original fibre stalk together with the expected dimension of its fibre
(Stacks, Tags 00RE, 00R7, 00RH and 00N8). -/
theorem polynomial_chart_flat_stalk_iff_fibre_depth_and_dimension
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) [IsAffine U.toScheme] (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    [LocallyOfFinitePresentation e] [LocallyQuasiFinite e]
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme) :
    (e.stalkMap x).hom.Flat ↔
      (IsLocalRing.depth
          (R := (f.fiber (f (U.ι x))).presheaf.stalk (f.asFiber (U.ι x)))
          ((f.fiber (f (U.ι x))).presheaf.stalk (f.asFiber (U.ι x))) : WithBot ℕ∞) =
        ringKrullDim ((f.fiber (f (U.ι x))).presheaf.stalk (f.asFiber (U.ι x))) ∧
      topologicalKrullDimAt (f.asFiber (U.ι x)) = (n : WithBot ℕ∞) := by
  let S := (f.fiber (f (U.ι x))).presheaf.stalk (f.asFiber (U.ι x))
  obtain ⟨R, hR, φ, hφ, d, r, t, hS, hd, hr, hzero, hle, htop, hn, hflat⟩ :=
    polynomial_chart_local_algebra f U n e he x
  let := hR
  let := hφ
  let := hS
  change (e.stalkMap x).hom.Flat ↔
    (IsLocalRing.depth (R := S) S : WithBot ℕ∞) = ringKrullDim S ∧ _
  constructor
  · intro hf
    have hf' := hflat.mp hf
    have hfaith : φ.FaithfullyFlat := by
      let : Algebra R S := φ.toAlgebra
      have : Module.Flat R S := hf'
      exact Module.FaithfullyFlat.of_flat_of_isLocalHom
    have hdimle := φ.ringKrullDim_le_of_faithfullyFlat_of_isLocalHom hfaith
    have hdim : ringKrullDim S = ringKrullDim R :=
      le_antisymm (by rw [hr, hd]; exact_mod_cast hle) hdimle
    have hrd : r = d := by exact_mod_cast hr.symm.trans (hdim.trans hd)
    obtain ⟨_, hlocal, _, hdepth⟩ := IsLocalRing.depth_eq_add_of_flat_local φ hf'
    let := hlocal
    have hfdepth := IsLocalRing.depth_le_supportDim
      (R := S ⧸ (IsLocalRing.maximalIdeal R).map φ)
      (S ⧸ (IsLocalRing.maximalIdeal R).map φ)
    rw [Module.supportDim_self_eq_ringKrullDim, hzero] at hfdepth
    have hfzero : IsLocalRing.depth (R := S ⧸ (IsLocalRing.maximalIdeal R).map φ)
        (S ⧸ (IsLocalRing.maximalIdeal R).map φ) = 0 :=
      le_antisymm (WithBot.coe_le_coe.mp hfdepth) zero_le
    rw [regular_local_depth_eq R d hd, hfzero, add_zero] at hdepth
    refine ⟨?_, ?_⟩
    · calc
        (IsLocalRing.depth (R := S) S : WithBot ℕ∞) =
            ((d : ℕ∞) : WithBot ℕ∞) := congrArg (fun z : ℕ∞ ↦ (z : WithBot ℕ∞)) hdepth
        _ = ringKrullDim S := by rw [hdim, hd]; simp
    · rw [htop, hrd, hn]
  · rintro ⟨hdepth, hdim⟩
    have hsum : r + t = n := by exact_mod_cast htop.symm.trans hdim
    have hrd : r = d := by omega
    have hdepth' : IsLocalRing.depth (R := S) S = (r : ℕ∞) :=
      WithBot.coe_injective (hdepth.trans hr)
    apply hflat.mpr
    apply RingHom.flat_of_regular_of_depth_ge φ r hr (by rw [hdepth'])
    rw [hzero, add_zero, hr, hd, hrd]

end AlgebraicGeometry
