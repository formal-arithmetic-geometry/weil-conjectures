/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.BoundedAbelianClosedEffacement
import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder

/-! # The finite-coefficient successor step for henselian comparison -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The successor step assumes comparison only in the preceding degree,
uniformly for abelian sheaves killed by the fixed integer `n`
(Stacks, Tags 09ZE and 09ZI). -/
theorem bijective_cohomologyMap_succ_of_henselianRing_of_nsmul_eq_zero
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    (n : ℕ) (hn : 0 < n) (q : ℕ)
    (hprev : ∀ (F : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}),
      n • 𝟙 F = 0 → Function.Bijective
        (cohomologyMap (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F q))
    (G : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : n • 𝟙 G = 0) :
    Function.Bijective
      (cohomologyMap (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) G (q + 1)) := by
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : IsClosedImmersion i :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have bounded_cokernel {G' : Sheaf (Spec (.of A)).smallEtaleTopology
      AddCommGrpCat.{u + 1}} (a : G ⟶ G') (hG' : n • 𝟙 G' = 0) :
      n • 𝟙 (cokernel a) = 0 := by
    apply (cancel_epi (cokernel.π a)).mp
    rw [Preadditive.comp_nsmul, Category.comp_id, ← Category.id_comp (cokernel.π a),
      ← Preadditive.nsmul_comp, hG', zero_comp, comp_zero]
  refine ⟨(injective_iff_map_eq_zero _).2 ?_, ?_⟩
  · intro x hx
    obtain ⟨G', a, ha, hG', hkill⟩ := exists_bounded_mono_closed_cohomology_eq_zero
      (𝟙 (Spec (.of A))) n hn G hG (q + 1) (Nat.zero_lt_succ q)
      (cohomologyMap (𝟙 _) G (q + 1) x)
    have hax : Sheaf.H.map a (q + 1) x = 0 := by
      rw [← cohomologyMap_map] at hkill
      exact (cohomologyMap_bijective (𝟙 _) G' (q + 1)).1
        (hkill.trans (map_zero _).symm)
    let S := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel a }
    obtain ⟨hY, δX, δY, _, _, _, _, hEX, hEY, _, hg, hδ⟩ :=
      pullbackCohomology_longExact_ladder i S hS
    obtain ⟨y, hy⟩ := ((hEX q).2.2 x).mp hax
    have hy0 : δY q (cohomologyMap i S.X₃ q y) = 0 := by
      rw [← hδ, hy]
      exact hx
    obtain ⟨z0, hz0⟩ := ((hEY q).2.1 _).mp hy0
    obtain ⟨z, hz⟩ := (hprev G' hG').2 z0
    have hzy : Sheaf.H.map S.g q z = y := by
      apply (hprev (cokernel a) (bounded_cokernel a hG')).1
      exact (hg q z).trans (by rw [hz]; exact hz0)
    rw [← hy, ← hzy]
    exact ((hEX q).2.1 _).mpr ⟨z, rfl⟩
  · intro x0
    obtain ⟨G', a, ha, hG', hkill⟩ := exists_bounded_mono_closed_cohomology_eq_zero
      i n hn G hG (q + 1) (Nat.zero_lt_succ q) x0
    let S := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel a }
    obtain ⟨hY, δX, δY, _, _, _, _, hEX, hEY, _, _, hδ⟩ :=
      pullbackCohomology_longExact_ladder i S hS
    obtain ⟨y0, hy0⟩ := ((hEY q).2.2 x0).mp hkill
    obtain ⟨y, hy⟩ := (hprev (cokernel a) (bounded_cokernel a hG')).2 y0
    refine ⟨δX q y, ?_⟩
    rw [hδ, hy, hy0]

end AlgebraicGeometry.Etale
