/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence

/-!
# Regular quotients from parameter approximations

Source: Milne, Algebraic Groups (2017), Lemma 13.3, printed p.255, and 13.2, printed p.254
(blueprint: lem-sfb-regular-quotient-parameter-approximation).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace IsRegularLocalRing

/-- An ideal agreeing in every finite jet with the span of the first `s` members of
some lifted cotangent basis has regular local quotient of dimension `d - s`.
The lifted basis may depend on the jet order; no compatibility is required.

Source: Milne, Algebraic Groups (2017), Lemma 13.3, printed p.255, with 13.2, printed p.254
(blueprint: lem-sfb-regular-quotient-parameter-approximation).

Proof: Write `B = A/J`. The quotient-local and Noetherian-image lemmas make `B` a nonzero
Noetherian local ring with residue field equal to that of `A`. The graded cotangent
criterion gives `dim A = d`. For each `n ≥ 1`, Nakayama applied to the finitely generated
maximal ideal shows that the full lifted cotangent basis generates that ideal. Thus the
parameter-quotient theorem makes the quotient `C_n` by its first `s` members regular local
of dimension `d - s`.

The assumed equality modulo the `(n + 1)`-st power also holds modulo the square. Adding
the `n`-th power shows that the degree-one and degree-`n` cotangent graded pieces for `B`
and `C_n` identify over the same residue field: both are the quotients of the corresponding
sums of ideals. The kernel of the map from the `q`-th power is its intersection with the
sum of the quotient ideal and the `(q + 1)`-st power, for `q = 1, n`.

Under these identifications, multiplication of representatives identifies the canonical
maps from the degree-`n` symmetric powers: both send a product of classes to the class
of the product, and such products span. The graded criterion makes this map an
isomorphism for regular `C_n`, hence for `B`, for every `n ≥ 1`. Its converse makes `B`
regular local. At `n = 1`, the cotangent space of `B` has basis the remaining `d - s`
classes, giving the asserted Krull dimension. This uses a separate tuple for each degree
and applies also when the initial tuple or its complementary tuple is empty. -/
theorem quotient_of_parameter_approximation
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (d : ℕ) (hd : d = Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A))
    (J : Ideal A) (hJ : J ≤ IsLocalRing.maximalIdeal A)
    (s : ℕ) (hs : s ≤ d)
    (happrox : ∀ n : ℕ, 1 ≤ n →
      ∃ (v : Fin d → IsLocalRing.maximalIdeal A)
        (b : Module.Basis (Fin d) (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A)),
        (∀ i : Fin d, b i = (IsLocalRing.maximalIdeal A).toCotangent (v i)) ∧
          J ⊔ IsLocalRing.maximalIdeal A ^ (n + 1) =
            Ideal.span (Set.range (fun i : Fin s ↦ (v (Fin.castLE hs i) : A))) ⊔
              IsLocalRing.maximalIdeal A ^ (n + 1)) :
    IsRegularLocalRing (A ⧸ J) ∧ ringKrullDim (A ⧸ J) = ((d - s : ℕ) : WithBot ℕ∞) := by
  sorry

end IsRegularLocalRing
