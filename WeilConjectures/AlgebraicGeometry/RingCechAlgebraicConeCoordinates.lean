/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingCechConeLinearEquiv
import WeilConjectures.AlgebraicGeometry.RingCechConeDifferential

/-! # Ordered localization coordinates for an algebraic two-row cone

.

## References

* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open scoped BigOperators TensorProduct
namespace CategoryTheory

/-- The algebraic cone of localization has the full ordered-subset coordinates.
This statement involves only modules, linear maps and localizations; it does not
involve a site, a sheaf tensor product or a totalization.

. -/
theorem ringCechAlgebraicCone_coordinates (A : CommRingCat.{u}) (r : ℕ)
    (f : Fin (r + 1) → A)
    (d : ∀ n : ℕ, ringCechTailTerm A r (fun i ↦ f i.succ) n →ₗ[A]
      ringCechTailTerm A r (fun i ↦ f i.succ) (n + 1))
    (l : ∀ (q : ℕ) (t : Fin (q + 2) ↪o Fin r) (j : Fin (q + 2)),
      Localization.Away (∏ i, f (t (Fin.succAboveOrderEmb j i)).succ) →ₐ[A]
        Localization.Away (∏ i, f (t i).succ))
    (hd₀ : ∀ (x : A) (t : Fin 1 ↪o Fin r),
      d 0 x t = algebraMap A (Localization.Away (∏ i, f (t i).succ)) x)
    (hd : ∀ (q : ℕ) (x : ringCechTailTerm A r (fun i ↦ f i.succ) (q + 1))
      (t : Fin (q + 2) ↪o Fin r),
      d (q + 1) x t = ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
        l q t j (x ((Fin.succAboveOrderEmb j).trans t))) :
    let M := ringCechTailTerm A r (fun i ↦ f i.succ)
    let S := Localization.Away (f 0)
    ∃ (E : ∀ q : ℕ, (M (q + 1) × (S ⊗[A] M q)) ≃ₗ[A]
        ((t : Fin (q + 1) ↪o Fin (r + 1)) → Localization.Away (∏ i, f (t i))))
      (l' : ∀ (q : ℕ) (t : Fin (q + 2) ↪o Fin (r + 1)) (j : Fin (q + 2)),
        Localization.Away (∏ i, f (t (Fin.succAboveOrderEmb j i))) →ₐ[A]
          Localization.Away (∏ i, f (t i))),
      (∀ (x : A) (t : Fin 1 ↪o Fin (r + 1)),
        E 0 (d 0 x, 1 ⊗ₜ[A] x) t =
          algebraMap A (Localization.Away (∏ i, f (t i))) x) ∧
      (∀ (q : ℕ) (x : M (q + 1)) (y : S ⊗[A] M q)
        (t : Fin (q + 2) ↪o Fin (r + 1)),
        E (q + 1) (d (q + 1) x,
          1 ⊗ₜ[A] x - TensorProduct.map (LinearMap.id : S →ₗ[A] S) (d q) y) t =
          ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
            l' q t j (E q (x, y) ((Fin.succAboveOrderEmb j).trans t))) := by
  dsimp only
  have hD (n : ℕ) : d n = ringCechDifferential A r (fun i ↦ f i.succ) n := by
    apply LinearMap.ext
    intro x
    cases n with
    | zero =>
      funext t
      exact hd₀ x t
    | succ q =>
      funext t
      rw [hd, ringCechDifferential_succ]
      apply Finset.sum_congr rfl
      intro j _
      have hl : l q t j = ringCechFace A (fun i ↦ f i.succ) q t j :=
        ringCechLocMap_unique A _ _ _
      rw [hl]
  refine ⟨fun q ↦ ringCechConeEquiv A r q f, ringCechFace A f, ?_, ?_⟩
  · intro x t
    rw [hD 0]
    exact congrFun (ringCechConeEquiv_d_zero A r f x) t
  · intro q x y t
    rw [hD (q + 1), hD q]
    exact (congrFun (ringCechConeEquiv_d A r q f x y) t).trans
      (ringCechDifferential_succ A (r + 1) f q
        (ringCechConeEquiv A r q f (x, y)) t)

end CategoryTheory
