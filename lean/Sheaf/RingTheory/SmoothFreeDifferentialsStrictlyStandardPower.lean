/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Sheaf.RingTheory.StrictlyStandardElement

/-!
# Powers of an element with smooth free localization are strictly standard

Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07EZ
(blueprint: lem-weil-pbc-smooth-free-differentials-strictly-standard-power).

## Main statements

* `smooth_free_differentials_strictly_standard_power`.
-/

@[expose] public section

universe u v

namespace Algebra

/-- If the localization at `a` is smooth and its module of Kähler differentials is
stably free, then all sufficiently large powers of `a` are strictly standard.
Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07EZ, part (e)
(blueprint: lem-weil-pbc-smooth-free-differentials-strictly-standard-power).

Proof (Stacks Tag 07EZ(e)), following the node's six steps:

1. Choose a finite presentation `A = R[x₁, ..., xₙ]/I` using
   `def-weil-pbc-finitely-presented-algebra` and `def-weil-pbc-mv-polynomial-ring`.
   By `lem-weil-pbc-smooth-localization-conormal-split`, the localized conormal sequence
   splits: `(I/I²)ₐ × Ω[Aₐ/R]` is isomorphic to `Aₐⁿ`. The hypothesis gives
   `(I/I²)ₐ × Aₐᵗ ≃ Aₐⁿ⁺ˢ`, so the localized conormal module is stably free.
2. Add `r = t` variables sent to zero. The kernel is `J = (I, xₙ₊₁, ..., xₙ₊ᵣ)`.
   The isomorphism `J/J² ≃ (I/I²) × Aʳ` sends a relation to its constant term in the
   new variables and their linear coefficients modulo `I`. Its inverse takes lifts of
   those coefficients; changes of lifts lie in `J²`. Products of elements of `J` map
   to zero, so both maps descend. Localizing makes `(J/J²)ₐ` finite free
   (`def-weil-pbc-module-localization-away`).
3. Lift a basis of `(J/J²)ₐ` to `f₁, ..., f_c ∈ J`, clearing denominators; extend it
   to finitely many generators `f₁, ..., f_m` of `J`. Write `N = n + r`.
   The split conormal injection gives `c ≤ N` by reduction modulo a maximal ideal
   when `Aₐ` is nonzero; when `Aₐ = 0`, choose the empty basis. Thus `c ≤ min N m`.
4. The remaining relations lie in the span of the first `c` after localization.
   Clear denominators and localization torsion to obtain
   `hᵉ f_j ∈ (f₁, ..., f_c) + J²` for all `j > c` and all `e ≥ e₁`, where `h`
   lifts `a` (`def-weil-pbc-module-localization-away`). This is the second condition
   of `def-weil-pbc-strictly-standard-element` for `aᵉ`.
5. Let `D` be the Jacobian matrix of the first `c` relations
   (`def-weil-pbc-polynomial-partial-derivative`). The split conormal injection has a
   left inverse over `Aₐ`. Clear its denominators and localization torsion to get
   `B D = a^(e₂) 1_c` over `A`. By `lem-weil-pbc-matrix-left-inverse-minors` (2),
   `a^(c * e₂)` is a linear combination of the `c` by `c` minors of `D`.
   Multiplying the coefficients gives this condition for every `e ≥ c * e₂`.
   For `c = 0`, the empty minor is `1` and this condition is automatic.
6. Take `e₀ = max 1 (max e₁ (c * e₂))`. Both defining conditions hold for every
   `e ≥ e₀`, so `aᵉ` is strictly standard by `def-weil-pbc-strictly-standard-element`.
-/
theorem smooth_free_differentials_strictly_standard_power
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [FinitePresentation R A] (a : A)
    [Algebra.Smooth R (Localization.Away a)]
    (s t : ℕ)
    (hstable : Nonempty
      (KaehlerDifferential R (Localization.Away a) × (Fin s →₀ Localization.Away a)
        ≃ₗ[Localization.Away a] (Fin t →₀ Localization.Away a))) :
    ∃ e₀ : ℕ, 1 ≤ e₀ ∧ ∀ e : ℕ, e₀ ≤ e →
      IsStrictlyStandardElement (R := R) (a ^ e) := by
  sorry

end Algebra
