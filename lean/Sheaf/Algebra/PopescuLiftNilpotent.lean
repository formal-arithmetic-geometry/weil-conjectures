/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Basic

/-!
# Lifting ind-smoothness across nilpotent thickenings

Source: Stacks Project, Smoothing Ring Maps, Proposition Tag 07CM
(blueprint: lem-weil-pbc-popescu-lift-nilpotent).
-/

universe u v

open CategoryTheory

namespace Algebra

/-- If `R → Λ` is flat, `I ⊆ R` is nilpotent and `Λ / IΛ` is a filtered colimit of smooth
`R / I`-algebras, then `Λ` is a filtered colimit of smooth `R`-algebras.

Source: Stacks Project, Smoothing Ring Maps, Proposition Tag 07CM
(blueprint: lem-weil-pbc-popescu-lift-nilpotent).

Proof (the four steps of the node):
1. Square-zero case, criterion: for an ideal `K` with `K² = 0`, `Λ / KΛ` ind-smooth over
   `R / K` and `R → Λ` flat, by lem-weil-pbc-factorization-criterion-filtered-colimit
   (Algebra 07C3) applied to the set of smooth `R`-algebras that are quotients of finite
   polynomial rings, it suffices to factor every map `φ : A → Λ` from a finitely presented
   `R`-algebra through a smooth `R`-algebra.
2. Square-zero case, lift once: lem-weil-pbc-popescu-lift-once (07CK) factors `φ` as
   `A → B / J → Λ` with `B` smooth and `J ⊆ KB` finitely generated.
3. Square-zero case, lift twice: lem-weil-pbc-popescu-lift-twice (07CL), using flatness,
   gives `α : B → B'`, `β : B' → Λ` with `B'` smooth, `α(J) = 0` and `β ∘ α = (B → Λ)`;
   `α` factors through `B / J`, and `A → B / J → B' → Λ` is `φ`.
4. Induction on `n` with `I ^ n = 0`: `n = 1` is hypothesis (2); for `n ≥ 2` put
   `K = I ^ (n - 1)` (square zero); `R / K → Λ / KΛ` is flat by
   lem-weil-pbc-tensor-quotient-base-change and lem-weil-pbc-flat-module-base-change, its
   reduction by `I / K` is `Λ / IΛ`, so by induction `Λ / KΛ` is ind-smooth over `R / K`,
   and steps 1-3 for `K` conclude. -/
theorem popescu_lift_nilpotent
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) (hI : ∃ n : ℕ, 1 ≤ n ∧ I ^ n = ⊥)
    (hΛ :
      ObjectProperty.ind.{max u v}
        (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ Smooth (R ⧸ I) C)
        (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))
    (hflat : RingHom.Flat (algebraMap R Λ)) :
    ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} R ↦ Smooth R C) (CommAlgCat.of R Λ) := by
  sorry

end Algebra
