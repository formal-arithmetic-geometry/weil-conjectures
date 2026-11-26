/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.SquareZeroSmallModel

/-!
# Adic formal smoothness for test algebras in arbitrary universes

The definition `Algebra.FormallySmoothAdic` only quantifies over test algebras in universe
`max u v`. We show that the lifting property holds for test algebras in any universe.

## Implementation details

Choose representatives in `D` of the images of elements of `S` and let `A` be the
`R`-subalgebra they generate, with the square-zero ideal `J ∩ A`. Since `A` is a quotient of
the polynomial algebra `R[X_s | s ∈ S]`, it has a model in `Type (max u v)`
(`Algebra.exists_squareZero_small_model`), where the defining lifting property applies.

## References

* [Stacks, Tag 07EB]
-/

@[expose] public section

universe u v z

namespace Algebra

/-- Universe-polymorphic form of adic formal smoothness, needed when a lifting target
has a larger universe than the one occurring in the source definition: every continuous
`R`-algebra map `S → D ⧸ J` with `J ^ 2 = 0` lifts to `D`, for `D` in any universe. -/
theorem formallySmoothAdic_lift_universe
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (n : Ideal S) (h : FormallySmoothAdic R S n)
    (D : Type z) [CommRing D] [Algebra R D] (J : Ideal D) (hJ : J ^ 2 = ⊥)
    (g : S →ₐ[R] D ⧸ J)
    (hg : ∃ k : ℕ, 1 ≤ k ∧ ∀ x ∈ n ^ k, g x = 0) :
    ∃ f : S →ₐ[R] D, (Ideal.Quotient.mkₐ R J).comp f = g := by
  obtain ⟨D₀, instRing, instAlg, e, K, q, g₀, hK, hq, hqe, hqg⟩ :=
    exists_squareZero_small_model R S D J hJ g
  let := instRing
  let := instAlg
  obtain ⟨k, hk, hgk⟩ := hg
  have hg₀ : ∃ k : ℕ, 1 ≤ k ∧ ∀ x ∈ n ^ k, g₀ x = 0 := by
    refine ⟨k, hk, fun x hx ↦ hq ?_⟩
    have hxg : q (g₀ x) = g x := DFunLike.congr_fun hqg x
    rw [hxg, hgk x hx, map_zero]
  obtain ⟨f₀, hf₀⟩ := h K hK g₀ hg₀
  refine ⟨e.comp f₀, ?_⟩
  calc
    (Ideal.Quotient.mkₐ R J).comp (e.comp f₀) =
        ((Ideal.Quotient.mkₐ R J).comp e).comp f₀ := (AlgHom.comp_assoc _ _ _).symm
    _ = (q.comp (Ideal.Quotient.mkₐ R K)).comp f₀ := by rw [hqe]
    _ = q.comp ((Ideal.Quotient.mkₐ R K).comp f₀) := AlgHom.comp_assoc _ _ _
    _ = q.comp g₀ := by rw [hf₀]
    _ = g := hqg

end Algebra
