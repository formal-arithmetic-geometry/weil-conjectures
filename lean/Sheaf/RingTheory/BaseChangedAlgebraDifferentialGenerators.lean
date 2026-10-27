/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Chosen algebra generators and their differentials after scalar extension

Source: Stacks Project, Algebra, Tags 0C4F (`lemma-colimit-unramified`) and 00RX
(`lemma-differentials-polynomial-ring`), the generator paragraphs of their proofs
(blueprint: lem-trf-base-changed-algebra-differential-generators).
-/

@[expose] public section

universe u v w z

open scoped TensorProduct BigOperators

namespace KaehlerDifferential

/-- The differential clauses for a specified finite family: spanning, the monomial
Leibniz formula, its finite additive extension, and vanishing for the empty family.
The algebra structure is precisely that induced by `f`, with no extra choice.

Source: Stacks Project, Algebra, Tag 00RX, `lemma-differentials-polynomial-ring`,
first proof paragraph; Tag 0C4F, `lemma-colimit-unramified`, generator paragraph
(blueprint: lem-trf-base-changed-algebra-differential-generators). -/
def ChosenGeneratorFormulas {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) {m : ℕ} (x : Fin m → S) : Prop :=
  Submodule.span S (Set.range (fun r ↦ @D R S _ _ f.toAlgebra (x r))) = ⊤ ∧
  (∀ (b : R) (e : Fin m → ℕ),
    @D R S _ _ f.toAlgebra (f b * ∏ r, x r ^ e r) =
      ∑ r ∈ Finset.univ.filter (fun r ↦ 0 < e r),
        ((e r : S) * f b * (∏ s ∈ Finset.univ.erase r, x s ^ e s) *
          x r ^ (e r - 1)) • @D R S _ _ f.toAlgebra (x r)) ∧
  (∀ (s : Finset (Fin m → ℕ)) (b : (Fin m → ℕ) → R),
    @D R S _ _ f.toAlgebra (∑ e ∈ s, f (b e) * ∏ r, x r ^ e r) =
      ∑ e ∈ s, ∑ r ∈ Finset.univ.filter (fun r ↦ 0 < e r),
        ((e r : S) * f (b e) * (∏ j ∈ Finset.univ.erase r, x j ^ e j) *
          x r ^ (e r - 1)) • @D R S _ _ f.toAlgebra (x r)) ∧
  (m = 0 → Subsingleton (@KaehlerDifferential R S _ _ f.toAlgebra))

end KaehlerDifferential

namespace Algebra

/-- A chosen finite algebra generating family survives arbitrary scalar extension,
and its universal differentials span before and after extension, with the explicit
pure-tensor and monomial formulas. The case of no generators is included.

Source: Stacks Project, Algebra, Tag 0C4F, `lemma-colimit-unramified`, generator
paragraph; Tag 00RX, `lemma-differentials-polynomial-ring`, first proof paragraph
(blueprint: lem-trf-base-changed-algebra-differential-generators).

Proof:
1. For each exponent vector, multiply the pure tensors `1 ⊗ x r` to obtain
   `1 ⊗ ∏ r, x r ^ e r`, using the multiplication from the tensor construction
   `def-weil-pbc-module-tensor-product`. Multiplying by `t ⊗ b` and expanding
   in the second factor gives the asserted identity for every polynomial expression.
2. Every tensor is a finite sum of pure tensors; absorb module scalars into their
   first factors. Express each second factor as a polynomial using the hypothesis.
   Step 1 then proves generation over the extended coefficient ring. No flatness
   or injectivity is used.
3. In either algebra, the universal derivation of
   `def-weil-pbc-kahler-differentials` is additive, obeys Leibniz, and kills
   coefficients. Hence `d 1 = 0`, `d (b*z) = b*d z`, and induction on `n` gives
   `d (z^n) = n*z^(n-1)*d z` for positive `n`, with zero derivative for `n = 0`.
4. Induct on the finite product and apply step 3 to each factor. Omit zero
   exponents to get the displayed monomial formula; additivity gives its finite
   polynomial extension.
5. All universal differentials span the differential module by its quotient
   construction. Express each argument as a polynomial (using step 2 after base
   change); step 4 expresses its differential in the span of the chosen ones.
   For the empty family every polynomial is a coefficient, so all differentials
   vanish and both modules are zero.
-/
theorem baseChanged_algebra_differential_generators
    {A : Type u} {B : Type v} {C : Type w} {T : Type z}
    [CommRing A] [CommRing B] [CommRing C] [CommRing T]
    [Algebra A B] [Algebra A C] [Algebra A T]
    (φ : B →ₐ[A] C) (m : ℕ) (x : Fin m → C)
    (hx : Function.Surjective (MvPolynomial.eval₂Hom φ.toRingHom x)) :
    Function.Surjective
      (MvPolynomial.eval₂Hom
        (TensorProduct.map (AlgHom.id A T) φ).toRingHom
        (fun r ↦ (1 : T) ⊗ₜ[A] x r)) ∧
    (∀ (t : T) (c : C) (s : Finset (Fin m → ℕ)) (b : (Fin m → ℕ) → B),
      c = ∑ e ∈ s, φ (b e) * ∏ r, x r ^ e r →
      t ⊗ₜ[A] c = ∑ e ∈ s,
        TensorProduct.map (AlgHom.id A T) φ (t ⊗ₜ[A] b e) *
          ∏ r, ((1 : T) ⊗ₜ[A] x r) ^ e r) ∧
    KaehlerDifferential.ChosenGeneratorFormulas φ.toRingHom x ∧
    KaehlerDifferential.ChosenGeneratorFormulas
      (TensorProduct.map (AlgHom.id A T) φ).toRingHom
      (fun r ↦ (1 : T) ⊗ₜ[A] x r) := by
  sorry

end Algebra
