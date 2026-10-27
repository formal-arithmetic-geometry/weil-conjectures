/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations

import Mathlib.RingTheory.Filtration

/-!
# Artin--Rees principal-quotient colength difference

Source: Stacks Project, Algebra, Tag 00IN (lemma-Artin-Rees), specialized to a
principal ideal in a local domain, and the quotient sequence in Tag 00K6
(lemma-hilbert-ses), used in Tag 00KQ (proposition-dimension).
(blueprint: lem-trf-artin-rees-principal-colength-difference).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace IsLocalRing

/-- The Artin--Rees intersection bound and colength-difference estimate for a nonzero
nonunit `x` in a Noetherian local domain. The quotient ring is written literally as
`A ⧸ Ideal.span {x}` and its maximal ideal as the image of `maximalIdeal A`.
The submodule `Submodule.comap (Submodule.subtype (Ideal.span {x} : Submodule A A))
            (maximalIdeal A ^ n : Submodule A A)` is the intersection
`xA ∩ a^n` viewed inside `xA`, so its quotient is precisely the middle quotient.
All lengths are Mathlib's extended-natural module lengths; the finiteness hypotheses
and conclusion ensure the displayed subtractions are subtractions of finite integers.

Source: Stacks Project, Algebra, Tags 00IN (lemma-Artin-Rees), 00K6 (lemma-hilbert-ses),
00IV (lemma-length-additive), 00IX (lemma-length-independent), and 00KQ
(proposition-dimension).
(blueprint: lem-trf-artin-rees-principal-colength-difference).

Proof plan:
1. Apply `lem-weil-pbc-artin-rees`, namely `Ideal.exists_pow_inf_eq_pow_smul`, to
   `I = a`, `M = A`, and `N = xA`. Enlarge its constant to `c = max 1 c₀`.
   Monotonicity of ideal powers gives `xA ∩ a^n ≤ a^(n-c) xA` for `n > c`.
2. The quotient map identifies `B/b^n` with `A/(xA + a^n)`. Every `A`-submodule
   of a `B`-module is a `B`-submodule: lift each scalar along the surjection `A → B`.
   Thus the submodule chains defining `def-weil-pbc-module-length` coincide, giving
   the two scalar-restriction length equalities below. The ideal `(x)` is contained
   in the proper maximal ideal, so `B` is nonzero and local with maximal ideal `aB`.
3. The natural inclusion and projection give the short exact sequence
   `0 → xA/(xA ∩ a^n) → A/a^n → A/(xA + a^n) → 0`.
   Apply `lem-weil-pbc-length-additive-short-exact` (`Module.length_eq_add_of_exact`).
   Finiteness of `H_A(n)` makes both summands finite and yields the difference equality.
4. Set `r = n-c ≥ 1`. Multiplication by `x` gives a linear bijection
   `A/a^r ≃ xA/(a^r xA)`: surjectivity is immediate, and injectivity follows by
   cancelling the nonzero element `x` in the domain `A`. Its length is `H_A(r)`.
5. The inclusion from step 1 induces a surjection from the middle quotient onto
   `xA/(a^r xA)`. Apply length additivity to its kernel and quotient to bound the
   middle length below by `H_A(r)`.
6. Subtract the finite lengths in steps 3 and 5 to obtain the asserted inequality,
   with the same constant for every `n > c`.
-/
theorem exists_artinRees_principal_colength_difference
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (x : A) (hx : x ≠ 0) (hxm : x ∈ maximalIdeal A)
    (hA : ∀ n : ℕ, 1 ≤ n → Module.length A (A ⧸ maximalIdeal A ^ n) < ⊤)
    (hB : ∀ n : ℕ, 1 ≤ n →
      Module.length (A ⧸ Ideal.span {x})
        ((A ⧸ Ideal.span {x}) ⧸
          ((maximalIdeal A).map (Ideal.Quotient.mk (Ideal.span {x}))) ^ n) < ⊤) :
    IsLocalRing (A ⧸ Ideal.span {x}) ∧
      ((maximalIdeal A).map (Ideal.Quotient.mk (Ideal.span {x}))).IsMaximal ∧
      ∃ c : ℕ, 1 ≤ c ∧ ∀ n : ℕ, c < n →
        Ideal.span {x} ⊓ maximalIdeal A ^ n ≤
          maximalIdeal A ^ (n - c) * Ideal.span {x} ∧
        Module.length A ((Ideal.span {x}) ⧸
          Submodule.comap (Submodule.subtype (Ideal.span {x} : Submodule A A))
            (maximalIdeal A ^ n : Submodule A A)) < ⊤ ∧
        Module.length A
          ((A ⧸ Ideal.span {x}) ⧸
            ((maximalIdeal A).map (Ideal.Quotient.mk (Ideal.span {x}))) ^ n) =
          Module.length (A ⧸ Ideal.span {x})
            ((A ⧸ Ideal.span {x}) ⧸
              ((maximalIdeal A).map (Ideal.Quotient.mk (Ideal.span {x}))) ^ n) ∧
        Module.length A (A ⧸ (Ideal.span {x} ⊔ maximalIdeal A ^ n)) =
          Module.length (A ⧸ Ideal.span {x})
            ((A ⧸ Ideal.span {x}) ⧸
              ((maximalIdeal A).map (Ideal.Quotient.mk (Ideal.span {x}))) ^ n) ∧
        Module.length (A ⧸ Ideal.span {x})
          ((A ⧸ Ideal.span {x}) ⧸
            ((maximalIdeal A).map (Ideal.Quotient.mk (Ideal.span {x}))) ^ n) =
          Module.length A (A ⧸ maximalIdeal A ^ n) -
            Module.length A ((Ideal.span {x}) ⧸
              Submodule.comap (Submodule.subtype (Ideal.span {x} : Submodule A A))
                (maximalIdeal A ^ n : Submodule A A)) ∧
        Module.length (A ⧸ Ideal.span {x})
          ((A ⧸ Ideal.span {x}) ⧸
            ((maximalIdeal A).map (Ideal.Quotient.mk (Ideal.span {x}))) ^ n) ≤
          Module.length A (A ⧸ maximalIdeal A ^ n) -
            Module.length A (A ⧸ maximalIdeal A ^ (n - c)) := by
  sorry

end IsLocalRing
