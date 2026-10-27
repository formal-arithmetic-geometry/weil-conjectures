/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.Defs

/-! # A local polynomial cover of an essentially finite type local algebra

Source: Stacks Project, More on Morphisms, Tag 0GSG
(`lemma-mod-injective-valuation-ring`), first reduction paragraph
(blueprint: lem-trf-local-essentially-finite-type-polynomial-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- A local essentially finite type algebra is a quotient of a polynomial algebra localized
at a prime. Both maps are local, and the intermediate local algebra is essentially of finite
presentation. The final existential writes out the latter property: it is isomorphic as an
`A`-algebra to a localization of a finitely presented `A`-algebra. The maximal ideal of
`Localization.AtPrime q` is `q` extended to that localization, by
`Localization.AtPrime.map_eq_maximalIdeal`.

Source: Stacks Project, More on Morphisms, Tag 0GSG
(`lemma-mod-injective-valuation-ring`), first reduction paragraph
(blueprint: lem-trf-local-essentially-finite-type-polynomial-cover).

Proof:
1. Unpack def-weil-pbc-essentially-finite-type-algebra to obtain a finite type algebra
   `C`, a submonoid `W`, and an algebra isomorphism from its localization to `B`.
   By def-weil-pbc-finite-type-algebra choose a surjection `e : A[x_1,...,x_n] → C`.
   Compose with the localization map `j : C → B` to obtain `h = j ∘ e`.
2. Set `q = h⁻¹(maximalIdeal B)`. It is prime as the inverse image of a maximal ideal.
   For `s ∉ q`, `h(s)` is a unit by lem-weil-pbc-local-ring-unit-criterion.
3. Use lem-weil-pbc-ring-localization-universal-property and
   def-weil-pbc-localization-at-prime to extend `h` to `π : P_q → B`, sending `f/s` to
   `h(f) h(s)⁻¹`. This is an `A`-algebra map, since its values on constants agree with
   the given structure map `A → B`.
4. Write any `b ∈ B` as `j(c) j(w)⁻¹` with `w ∈ W`. Lift `c,w` to `f,s ∈ P`.
   Since `j(w)` is a unit, the local-ring unit criterion gives `s ∉ q`, and `π(f/s)=b`.
   Thus `π` is surjective; this uses the fraction description in
   def-weil-pbc-essentially-finite-type-algebra.
5. By def-weil-pbc-localization-at-prime the maximal ideal of `P_q` is `qP_q`.
   It maps into the maximal ideal of `B`. The inverse image of that maximal ideal
   under `π` is proper, hence equals `qP_q` by maximality. Pulling back along `A → P_q`
   and using that `π` is an `A`-algebra map gives the assumed locality equality for `A → B`.
6. The polynomial ring `P` is finitely presented over `A`, with its `n` generators
   and no relations, by def-weil-pbc-finitely-presented-algebra. Choose `C=P` and
   `W=q.primeCompl` in the final existential, with the identity algebra isomorphism.
   This exhibits `P_q` as a localization of a finitely presented algebra, including
   the case `n=0`.
-/
theorem exists_local_essentially_finite_type_polynomial_cover
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [EssFiniteType A B]
    (hlocal : Ideal.comap (algebraMap A B) (IsLocalRing.maximalIdeal B) =
      IsLocalRing.maximalIdeal A) :
    ∃ (n : ℕ) (q : Ideal (MvPolynomial (Fin n) A)) (_ : q.IsPrime)
      (π : Localization.AtPrime q →ₐ[A] B),
      Function.Surjective π ∧
      Ideal.comap (algebraMap A (Localization.AtPrime q))
        (IsLocalRing.maximalIdeal (Localization.AtPrime q)) = IsLocalRing.maximalIdeal A ∧
      Ideal.comap π.toRingHom (IsLocalRing.maximalIdeal B) =
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ∧
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
        FinitePresentation A C ∧
        ∃ W : Submonoid C, Nonempty (Localization W ≃ₐ[A] Localization.AtPrime q) := by
  sorry

end Algebra
