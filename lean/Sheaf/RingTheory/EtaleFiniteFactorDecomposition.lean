/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.RingTheory.Etale.Basic
import Sheaf.RingTheory.QuasiFiniteAtPrime

/-!
# A finite factor after an étale base change

Source: Stacks Project, Algebra, Lemma 10.145.3 (Tag 00UK), with the finite factors combined
(blueprint: lem-weil-pbc-finite-type-etale-finite-factor-decomposition).
-/

universe u v

open scoped TensorProduct

namespace Algebra

/-- (blueprint: lem-weil-pbc-finite-type-etale-finite-factor-decomposition)
Stacks Project, Algebra, Tag 00UK: a finite-type algebra admits, after an étale neighbourhood
of a prime with unchanged residue field, a decomposition into a finite algebra and an algebra
which is not quasi-finite at any prime above the chosen prime. The finite-type witness for
`B` records a consequence of the product decomposition, needed by `IsQuasiFiniteAtPrime`.

Proof from the node, step by step:
1. The fibre `κ(p) ⊗[R] S` has finitely many isolated points by
   `lem-weil-pbc-finite-type-field-finite-isolated-points`. The correspondence
   `lem-weil-pbc-fibre-ring-primes-bijection` identifies them with primes above `p` where
   the map is quasi-finite. Induct on an upper bound for their number.
2. If the bound is zero, take `R' = R`, `P = p`, the zero ring as `A`, and `B = S`.
   The identity is étale and induces the identity on residue fields.
3. Otherwise choose one isolated fibre prime and apply
   `lem-weil-pbc-etale-quasi-finite-finite-one-prime` (Tag 00UJ). Its idempotent `e` splits
   `C = R₁ ⊗[R] S` into the finite factor `C_e` and the finite-type factor `D = C_(1-e)`.
4. The unchanged residue field identifies the new fibre with the old one. The fibre of `D`
   is the complementary clopen factor and omits the selected isolated point. Thus the bound
   for its isolated points drops by one (use `lem-weil-pbc-fibre-ring-primes-bijection`).
5. Apply induction to `D`. Use `lem-weil-pbc-algebra-tensor-product-distributes-product`
   to assemble the finite factor from the base change of `C_e` and the finite factor supplied
   by induction. Finiteness survives base change and finite products. The composite is étale
   by `lem-weil-pbc-etale-composition-cancellation`; the residue-field isomorphisms compose.
6. The complementary factor is the one from induction, so it has no quasi-finite prime
   above the selected prime. This proves the final clause. -/
theorem exists_etale_finiteFactor_decomposition
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (P : Ideal R') (_ : P.IsPrime) (_ : P.LiesOver p)
      (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R' A)
      (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R' B)
      (_ : Algebra.FiniteType R' B),
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId R R') (P.over_def p)) ∧
      Nonempty ((R' ⊗[R] S) ≃ₐ[R'] (A × B)) ∧ Module.Finite R' A ∧
      ∀ q : PrimeSpectrum B, q.asIdeal.LiesOver P → ¬ IsQuasiFiniteAtPrime R' B q := by
  sorry

end Algebra
