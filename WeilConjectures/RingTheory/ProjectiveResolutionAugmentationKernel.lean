/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Augment
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# The bounded resolution of an augmentation kernel

Removing degree zero from a projective resolution gives a projective resolution of the
augmentation kernel.

## Implementation details

The truncated complex has new degree `i` equal to old degree `i + 1`. The old differential
`P_1 → P_0` factors surjectively through the kernel of `P_0 → M`, and the next differential has
the same kernel after this factorization since the kernel inclusion is monic.

## References

* [Stacks, Tag 0D1U] (the successor argument)
* [Stacks, Tag 065S] (1)
-/

@[expose] public section

universe u v

namespace ModuleCat

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

/-- Removing degree zero from a length-`n+1` projective resolution gives a
length-`n` projective resolution of its augmentation kernel. This works in an
independent module universe and needs no enough-projectives instance. -/
theorem hasProjectiveResolutionLE_augmentation_kernel
    {R : Type u} [CommRing R] {M : ModuleCat.{v} R} (n : ℕ)
    (P : ProjectiveResolution M)
    (hP : ∀ i : ℕ, n + 1 < i → IsZero (P.complex.X i)) :
    HasProjectiveResolutionLE (kernel (P.π.f 0)) n := by
  let K := ChainComplex.truncate.obj P.complex
  let a : K.X 0 ⟶ kernel (P.π.f 0) :=
    kernel.lift _ (P.complex.d 1 0) P.complex_d_comp_π_f_zero
  have ha : a ≫ kernel.ι (P.π.f 0) = P.complex.d 1 0 := by
    simp [a]
  have hw : K.d 1 0 ≫ a = 0 := by
    apply (cancel_mono (kernel.ι (P.π.f 0))).mp
    rw [assoc, ha, zero_comp]
    exact P.complex.d_comp_d 2 1 0
  have hepi : Epi a := by
    exact P.exact₀.epi_kernelLift
  have hex : (ShortComplex.mk (K.d 1 0) a hw).Exact := by
    let φ : ShortComplex.mk (K.d 1 0) a hw ⟶
        ShortComplex.mk (P.complex.d 2 1) (P.complex.d 1 0)
          (P.complex.d_comp_d 2 1 0) :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι (P.π.f 0) }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 (P.exact_succ 0)
  let π := (ChainComplex.toSingle₀Equiv K (kernel (P.π.f 0))).symm ⟨a, hw⟩
  have hπ : QuasiIso π := by
    constructor
    intro i
    cases i with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · exact ⟨hex, hepi⟩
      all_goals simp [K, ChainComplex.truncate, HomologicalComplex.shortComplexFunctor']
    | succ i =>
      rw [quasiIsoAt_iff_exactAt' π (i + 1)
        (ChainComplex.exactAt_succ_single_obj _ _)]
      rw [HomologicalComplex.exactAt_iff' K (i + 2) (i + 1) i (by simp) (by simp)]
      exact P.exact_succ (i + 1)
  refine ⟨{
    complex := K
    π := π
    quasiIso := hπ
    projective := fun i ↦ P.projective (i + 1) }, ?_⟩
  intro i hi
  exact hP (i + 1) (by omega)

end ModuleCat
