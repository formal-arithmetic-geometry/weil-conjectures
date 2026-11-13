/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# The reduced induced closed subscheme

Quasi-coherent ideal sheaves are represented by `Scheme.IdealSheafData`: their affine
ideals localize on basic opens. `idealOfOpens` gives their sections on arbitrary opens.

## References

* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 01J4](https://stacks.math.columbia.edu/tag/01J4)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The vanishing ideal is the quasi-coherent sheaf of sections vanishing at the points of `T`.
On each affine open its ideal is the unique radical ideal with the specified zero locus, and it
localizes on basic opens. Its closed subscheme is reduced, has image `T`, and is unique up to a
unique isomorphism over `X`. -/
theorem reduced_induced_closed_subscheme (X : Scheme.{u}) (T : TopologicalSpace.Closeds X) :
    (∀ (U : X.Opens) (f : Γ(X, U)),
      f ∈ (vanishingIdeal T).idealOfOpens U ↔
        ∀ (t : X) (ht : t ∈ U), t ∈ T → X.evaluation U t ht f = 0) ∧
    (∀ U : X.affineOpens,
      (∃! I : Ideal Γ(X, U), I.IsRadical ∧
        PrimeSpectrum.zeroLocus (I : Set Γ(X, U)) = U.2.fromSpec ⁻¹' (T : Set X)) ∧
      (vanishingIdeal T).ideal U = PrimeSpectrum.vanishingIdeal
        (U.2.fromSpec ⁻¹' (T : Set X)) ∧
      (∀ g : Γ(X, U),
        ((vanishingIdeal T).ideal U).map
          (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom =
            (vanishingIdeal T).ideal (X.affineBasicOpen g))) ∧
    IsClosedImmersion (vanishingIdeal T).subschemeι ∧
    IsReduced (vanishingIdeal T).subscheme ∧
    (vanishingIdeal T).subschemeι.ker = vanishingIdeal T ∧
    Set.range (vanishingIdeal T).subschemeι = (T : Set X) ∧
    (∀ U : X.affineOpens,
      IsPullback ((vanishingIdeal T).subschemeCover.f U)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((vanishingIdeal T).ideal U))))
        (vanishingIdeal T).subschemeι U.2.fromSpec) ∧
    (∀ (Z' : Scheme.{u}) (i' : Z' ⟶ X) [IsClosedImmersion i'] [IsReduced Z'],
      Set.range i' = (T : Set X) →
        i'.ker = vanishingIdeal T ∧
          ∃! φ : Z' ≅ (vanishingIdeal T).subscheme,
            φ.hom ≫ (vanishingIdeal T).subschemeι = i') := by
  classical
  have hrange : Set.range (vanishingIdeal T).subschemeι = (T : Set X) := by
    simp
  refine ⟨?_, ?_, inferInstance, inferInstance, ker_subschemeι _, hrange,
    fun U ↦ isPullback_subschemeCover_map _ U, ?_⟩
  · intro U f
    rw [mem_idealOfOpens_iff, ← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]
    constructor
    · intro h t ht hT
      rw [X.evaluation_eq_zero_iff_notMem_basicOpen]
      have hT' : t ∈ Set.range (vanishingIdeal T).subschemeι := by
        change t ∈ (T : Set X) at hT
        rwa [hrange]
      obtain ⟨z, rfl⟩ := hT'
      intro hz
      have : z ∈ (vanishingIdeal T).subschemeι ⁻¹ᵁ X.basicOpen f := hz
      rw [h] at this
      exact this
    · intro h
      apply le_antisymm _ bot_le
      intro z hz
      exact (X.evaluation_eq_zero_iff_notMem_basicOpen _
        (X.basicOpen_le f hz) f).mp
          (h _ (X.basicOpen_le f hz) (by
            change (vanishingIdeal T).subschemeι z ∈ (T : Set X)
            rw [← hrange]
            exact Set.mem_range_self z)) hz
  · intro U
    refine ⟨?_, rfl, fun g ↦ (vanishingIdeal T).map_ideal_basicOpen U g⟩
    let S := U.2.fromSpec ⁻¹' (T : Set X)
    have hc : IsClosed S := T.isClosed.preimage U.2.fromSpec.continuous
    have hv : PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal S :
        Set Γ(X, U)) = S := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hc.closure_eq]
    refine ⟨PrimeSpectrum.vanishingIdeal S,
      ⟨PrimeSpectrum.isRadical_vanishingIdeal _, hv⟩, ?_⟩
    intro I hI
    calc
      I = I.radical := hI.1.radical.symm
      _ = PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (I : Set Γ(X, U))) :=
        (PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical I).symm
      _ = PrimeSpectrum.vanishingIdeal S := congrArg _ hI.2
  · intro Z' i' _ _ hi
    have hk : i'.ker = vanishingIdeal T := by
      rw [i'.ker_eq_vanishingIdeal]
      congr 1
      apply TopologicalSpace.Closeds.ext
      change closure (Set.range i') = (T : Set X)
      rw [hi, T.isClosed.closure_eq]
    refine ⟨hk, ?_⟩
    let l := IsClosedImmersion.lift (vanishingIdeal T).subschemeι i'
      (by rw [ker_subschemeι, hk])
    have hl : l ≫ (vanishingIdeal T).subschemeι = i' :=
      IsClosedImmersion.lift_fac _ _ _
    have : IsIso l := IsClosedImmersion.isIso_of_ker_eq i' _ l hl
      (by rw [ker_subschemeι, hk])
    refine ⟨asIso l, hl, ?_⟩
    intro φ hφ
    apply Iso.ext
    apply (cancel_mono (vanishingIdeal T).subschemeι).mp
    exact hφ.trans hl.symm

end AlgebraicGeometry.Scheme.IdealSheafData
