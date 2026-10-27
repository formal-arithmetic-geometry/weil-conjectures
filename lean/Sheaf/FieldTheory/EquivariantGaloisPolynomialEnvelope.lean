/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Sheaf.FieldTheory.FieldTower
import WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions
import Mathlib.FieldTheory.SeparableDegree

/-!
# An equivariant finite Galois polynomial envelope

Source: de Jong, Families of curves and alterations, Lemma 5.6, printed p.614;
Stacks Project, Fields, Tags 09I3 and 0BME(2).
(blueprint: lem-sfb-equivariant-galois-polynomial-envelope)

## Main statements

* `exists_equivariant_galois_polynomial_envelope` constructs a common finite Galois
  extension, together with the group of compatible automorphism pairs. The given
  field action need not be faithful, and the polynomial family may be empty.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z t

/-- A finite group action on a field admits a finite Galois envelope splitting a finite
family of polynomial quotient algebras, with the compatible-pair group and its kernel.
Source: de Jong, Lemma 5.6, printed p.614; Stacks Fields 09I3 and 0BME(2).
(blueprint: lem-sfb-equivariant-galois-polynomial-envelope)

Proof:
1. Apply `lem-wf-finite-field-action-fixed-degree` to the image of the action on K.
   This image acts faithfully and has the same fixed field F as H, so K/F is finite Galois.
2. By `lem-zl-separable-permanence`, all E i b are separable over F. Products of finite
   spanning sets show they are finite over F. Apply
   `lem-weil-pbc-finite-galois-receiving-separable-extensions` to K and all E i b to get
   a finite Galois extension M/F receiving them. Include K even when I is empty.
3. The initial F-embeddings of E i b may disagree on K. By
   `lem-sfb-normal-intermediate-isomorphism-lifts`, extend the isomorphism from each
   embedded copy of K to the specified copy to an F-automorphism of M. Composing
   corrects every embedding to a K-embedding for that same specified copy.
4. By `lem-dl-a1-galois-over-intermediate`, M/K is Galois; an F-spanning set also
   spans over K, so M/K is finite.
5. In each product algebra take the coordinates of the residue class of T. Their
   minimal polynomials have a product annihilating that class, so f i divides that
   product. By normality all these minimal polynomials split in M. Apply
   `lem-trf-divisor-of-split-polynomial`; monicity and degree give the displayed
   factorization with exactly d i factors, allowing repetitions.
6. Compatible pairs are closed under componentwise products and inverses and contain
   the identity. Their subgroup J is finite by `lem-weil-pbc-finite-galois-fixed-field`
   for M/F. Its two projection homomorphisms give rho and the asserted action.
7. Every H-automorphism of K fixes F. Extend it to an F-automorphism of M by
   `lem-sfb-normal-intermediate-isomorphism-lifts`, proving rho surjective.
8. The kernel consists exactly of pairs (1,sigma) with sigma fixing K. The second
   projection identifies it with Aut_K(M). Apply
   `lem-weil-pbc-finite-galois-fixed-field` to M/K to identify its fixed elements
   with the image of the specified algebraMap K M. All embeddings fix this same K.
-/
theorem exists_equivariant_galois_polynomial_envelope
    (K : Type u) [Field K] (H : Type t) [Group H] [Finite H]
    [MulSemiringAction H K]
    (I : Type w) [Finite I] (f : I → Polynomial K) (d : I → ℕ)
    (hmonic : ∀ i : I, (f i).Monic) (hdegree : ∀ i : I, (f i).natDegree = d i)
    (hpositive : ∀ i : I, 1 ≤ d i)
    (B : I → Type z) [∀ i : I, Finite (B i)] [∀ i : I, Nonempty (B i)]
    (E : (i : I) → B i → Type v) [∀ (i : I) (b : B i), Field (E i b)]
    [∀ (i : I) (b : B i), Algebra K (E i b)]
    (hfinite : ∀ (i : I) (b : B i), FiniteDimensional K (E i b))
    (hseparable : ∀ (i : I) (b : B i), Algebra.IsSeparable K (E i b))
    (quotientEquiv : ∀ i : I,
      (Polynomial K ⧸ Ideal.span {f i}) ≃ₐ[K] ((b : B i) → E i b)) :
    ∃ (M : Type (max u v)) (_ : Field M) (_ : Algebra K M)
      (_ : Algebra (FixedPoints.subfield H K) M)
      (_ : IsScalarTower (FixedPoints.subfield H K) K M),
      FiniteDimensional (FixedPoints.subfield H K) M ∧
      IsGalois (FixedPoints.subfield H K) M ∧
      FiniteDimensional K M ∧ IsGalois K M ∧
      (∀ (i : I) (b : B i), Nonempty (E i b →ₐ[K] M)) ∧
      (∃ beta : (i : I) → Fin (d i) → M, ∀ i : I,
        (f i).map (algebraMap K M) =
          ∏ nu : Fin (d i), (Polynomial.X - Polynomial.C (beta i nu))) ∧
      ∃ (J : Subgroup (H × (M ≃ₐ[FixedPoints.subfield H K] M)))
        (rho : J →* H) (action : J →* (M ≃ₐ[FixedPoints.subfield H K] M)),
        (∀ p : H × (M ≃ₐ[FixedPoints.subfield H K] M),
          p ∈ J ↔ ∀ x : K, p.2 (algebraMap K M x) = algebraMap K M (p.1 • x)) ∧
        Finite J ∧
        (∀ g : J, rho g = g.val.1) ∧ Function.Surjective rho ∧
        (∀ g : J, action g = g.val.2) ∧
        (∀ (g : J) (x : K),
          action g (algebraMap K M x) = algebraMap K M (rho g • x)) ∧
        ∃ e : rho.ker ≃* (M ≃ₐ[K] M),
          (∀ (n : rho.ker) (x : M), e n x = n.val.val.2 x) ∧
          (∀ y : M, (∀ n : rho.ker, n.val.val.2 y = y) ↔
            y ∈ Set.range (algebraMap K M)) := by
  sorry
