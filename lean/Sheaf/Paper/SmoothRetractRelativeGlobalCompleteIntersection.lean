/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Smooth.Basic
import Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation

/-!
# Smooth retract by a relative global complete intersection

Source: Stacks Project, Smoothing Ring Maps, Lemma 07CG (lemma-syntomic-complete-intersection),
line 567 and proof lines 580--588 (blueprint:
lem-weil-pbc-smooth-retract-relative-global-complete-intersection).
-/

universe u v

namespace Algebra

/-- A smooth algebra is a retract of a relative global complete intersection that is smooth over it.
Source: Stacks Project, Smoothing Ring Maps, Lemma 07CG
(blueprint: lem-weil-pbc-smooth-retract-relative-global-complete-intersection).

Proof:
1. Apply lem-weil-pbc-improve-presentation-smooth-conormal-free to obtain a smooth
   `A`-algebra `C₀` with an `A`-algebra retraction and a polynomial presentation with free
   conormal module. Composition of smooth maps makes `C₀` smooth, hence finitely presented,
   over `R` (lem-weil-pbc-smooth-ring-map-base-change-composition).
2. Apply lem-weil-pbc-conormal-free-presentation-basis (07CF) to get `n,c,f` and an
   `R`-algebra isomorphism `ψ : R[x]/(f) ≃ C₀` with equation classes a conormal basis.
   Transport smoothness over `R` across `ψ`.
3. Set `σ = ψ⁻¹ ∘ (A → C₀)` and `π = ρ ∘ ψ`. Cancellation gives `π ∘ σ = id`.
   Give the quotient its `A`-algebra structure through `σ`; then `ψ` is an `A`-algebra
   isomorphism, so it transports smoothness over `A` as well.
4. By lem-weil-pbc-smooth-localization-conormal-split at `a = 1`,
   `J/J² ⊕ Ω[C/R] ≃ Cⁿ`. The basis identifies `J/J²` with `Cᶜ`. Tensoring at a prime
   with its residue field gives rank `Ω[C/R] = n - c` there.
5. For a prime of `R`, the fibre is smooth over its residue field by base change.
   By lem-weil-pbc-kahler-differentials-base-change its differentials have rank `n - c`.
   Lemma lem-weil-pbc-smooth-over-field-dimension-differentials identifies the dimension
   at every point of this fibre with that rank.
6. For a nonempty fibre, lem-weil-pbc-dimension-supremum-local-dimensions identifies
   its dimension with the supremum of these constant point dimensions, hence `n - c`.
   This is the specified relative global complete-intersection condition.
-/
theorem smooth_retract_relative_global_complete_intersection
    (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A] [Smooth R A] :
    ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R),
      IsRelativeGlobalCompleteIntersectionPresentation f ∧
      (∃ b : Module.Basis (Fin c)
          (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
          (Ideal.span (Set.range f)).Cotangent,
        ∀ j : Fin c,
          b j = (Ideal.span (Set.range f)).toCotangent
            ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩) ∧
      (∃ (σ : A →ₐ[R] (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))
          (π : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) →ₐ[R] A),
        π.comp σ = AlgHom.id R A ∧
        ∃ (_ : Algebra A (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))),
          (Algebra.ofId A (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))).toRingHom =
              σ.toRingHom ∧
          Smooth A (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) := by
  sorry

end Algebra
