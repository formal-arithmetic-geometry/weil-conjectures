/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltration
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentSupportAdicChain
import WeilConjectures.AlgebraicGeometry.CoherentGenericFilteredExtension
import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltrationExtension
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum

/-! # The irreducible-support step of coherent integral filtration

## References

* Stacks Project, Tags 01YF and 01YE
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Filter a coherent module with irreducible support, assuming smaller supports filtered
(Stacks, Tags 01YF, 01Y9 and 01YE). -/
theorem coherentIntegralFiltration_of_irreducible_support
    (X : Scheme.{u}) [IsNoetherian X]
    (T : TopologicalSpace.Closeds X) (ξ : X)
    (hξ : IsGenericPoint ξ (T : Set X))
    (hsmaller : ∀ (G : X.Modules), RingedSpace.IsCoherent X.toRingedSpace G →
      {x : X | ¬ Subsingleton (G.presheaf.stalk x)} ⊂ (T : Set X) →
      HasCoherentIntegralFiltration G)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hSupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} = (T : Set X)) :
    HasCoherentIntegralFiltration F := by
  classical
  have graded (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
      (hGT : {x : X | ¬ Subsingleton (G.presheaf.stalk x)} ⊆ (T : Set X))
      (hkill : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ),
        ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj G, a • m = 0) :
      HasCoherentIntegralFiltration G := by
    by_cases hfull : {x : X | ¬ Subsingleton (G.presheaf.stalk x)} = (T : Set X)
    · obtain ⟨A, Q, f, g, w, hs, hA, hQ, hAf, hQT⟩ :=
        coherent_generic_filtered_extension X T ξ hξ G hG hfull hkill
      exact coherentIntegralFiltration_of_shortExact X (ShortComplex.mk f g w)
        hs hA hG hQ hAf (hsmaller Q hQ hQT)
    · exact hsmaller G hG (Set.ssubset_iff_subset_ne.mpr ⟨hGT, hfull⟩)
  obtain ⟨n, P, hP0, hPn, hP, hstep⟩ := coherent_support_adic_chain X T ξ hξ F hF hSupp
  have hgood : ∀ k, k ≤ n → HasCoherentIntegralFiltration (P k) := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self =>
      have := Subobject.subsingleton_of_isZero hPn
      refine ⟨0, fun _ ↦ ⊥, fun _ _ _ ↦ le_rfl, rfl, Subsingleton.elim _ _, ?_, ?_⟩
      · intro j
        have hc := RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace
        exact hc.2.2.2.2 _ _ Subobject.botCoeIsoZero.symm hc.2.2.2.1
      · intro j
        exact Fin.elim0 j
    | @of_succ k hk ih =>
      obtain ⟨G, f, g, w, hs, hG, hGT, hkill⟩ := hstep k (Nat.lt_of_succ_le hk)
      exact coherentIntegralFiltration_of_shortExact X (ShortComplex.mk f g w)
        hs (hP (k + 1) hk) (hP k (Nat.le_trans (Nat.le_succ k) hk)) hG
        ih (graded G hG hGT hkill)
  simpa only [hP0] using hgood 0 (Nat.zero_le n)

end AlgebraicGeometry.Scheme.Modules
