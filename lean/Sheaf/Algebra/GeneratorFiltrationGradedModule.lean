/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Sheaf.Algebra.GeneratorFiltration
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Homogenizing a generator filtration

Source: Stacks Project, Tags 053E (proof of (2)) and 052N, explicit generator-filtration
realization of module homogenization.
(blueprint: lem-trf-generator-filtration-graded-module)
-/

@[expose] public section

universe u v w

open scoped DirectSum

namespace Module

/-- The generator filtration is increasing and exhaustive; its direct sum has the prescribed
homogenized polynomial action, internal integer grading, and the named degree-zero generators.
Torsion-freeness over a domain passes coefficientwise to this direct sum.
Source: Stacks Project, Tags 053E (proof of (2)) and 052N, explicit generator-filtration variant.
(blueprint: lem-trf-generator-filtration-graded-module)

Proof, following the seven elementary steps of the node:
1. Each spanning monomial of F_d is one of F_(d+1). Multiplication by b_i replaces its
   exponent alpha by alpha+e_i, proving both filtration inclusions by A-linearity.
2. Expand each B-coefficient of a finite expression in the m_j as a polynomial in the b_i.
   A bound on the finitely many total degrees puts the expression in some F_d; use d=0
   for an empty expression. This uses the three recorded finite-generation/polynomial nodes.
3. On x t^d define E_(k,alpha) by b^alpha x t^(d+k+|alpha|). The filtration inclusions
   make this well-defined and its support remains finite. Extend by the unique finite
   monomial expansion of each polynomial, using def-weil-pbc-mv-polynomial-ring.
4. Commutativity of B gives E_(k,alpha) E_(l,beta)=E_(k+l,alpha+beta), with E_(0,0)=id.
   Expand polynomial products to get the module laws. Constants act by the original A-action,
   and the variables give precisely the two displayed shifts.
5. Coefficient extraction proves the direct-sum grading is internal. A monomial of degree e
   shifts degree d to e+d, and linear combinations give the assertion for every homogeneous
   polynomial. Negative components are zero.
6. Each m_j lies in F_0. For |alpha|<=d, b^alpha m_j t^d equals
   X_0^(d-|alpha|) X^alpha times m_j t^0. Expand the coefficients of every finite sum to
   obtain the displayed finite generator expression (def-weil-finitely-generated-module).
7. If a nonzero scalar kills a finite sum, it kills each coefficient. Torsion-freeness of M
   makes every coefficient zero, giving injectivity of that scalar on the direct sum. -/
theorem generatorFiltrationGradedModule
    (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
    (M : Type w) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (n r : ℕ) (b : Fin n → B) (m : Fin r → M)
    (hb : Algebra.adjoin A (Set.range b) = ⊤)
    (hm : Submodule.span B (Set.range m) = ⊤) :
    ∃ (hF : ∀ d, generatorFiltration A b m d ≤ generatorFiltration A b m (d + 1))
      (hB : ∀ (i : Fin n) (d : ℕ) (x : generatorFiltration A b m d),
        b i • (x : M) ∈ generatorFiltration A b m (d + 1)),
      (∀ x : M, ∃ d : ℕ, x ∈ generatorFiltration A b m d) ∧
      (∃ (modN : Module (MvPolynomial (Option (Fin n)) A)
          (⨁ d : ℕ, generatorFiltration A b m d))
        (G : ℤ → Submodule A (⨁ d : ℕ, generatorFiltration A b m d)),
        (∀ (a : A) (z : ⨁ d : ℕ, generatorFiltration A b m d),
          @SMul.smul _ _ modN.toSMul (MvPolynomial.C a) z = a • z) ∧
        (∀ (d : ℕ) (x : generatorFiltration A b m d),
          @SMul.smul _ _ modN.toSMul (MvPolynomial.X none)
            (DirectSum.of (fun k ↦ generatorFiltration A b m k) d x) =
          DirectSum.of (fun k ↦ generatorFiltration A b m k) (d + 1)
            ⟨(x : M), hF d x.property⟩) ∧
        (∀ (i : Fin n) (d : ℕ) (x : generatorFiltration A b m d),
          @SMul.smul _ _ modN.toSMul (MvPolynomial.X (some i))
            (DirectSum.of (fun k ↦ generatorFiltration A b m k) d x) =
          DirectSum.of (fun k ↦ generatorFiltration A b m k) (d + 1)
            ⟨b i • (x : M), hB i d x⟩) ∧
        (∀ d : ℤ, G d = if 0 ≤ d then
          LinearMap.range (DirectSum.lof A ℕ (fun k ↦ generatorFiltration A b m k) d.toNat)
          else ⊥) ∧
        DirectSum.IsInternal G ∧
        (∀ (e : ℕ) (d : ℤ)
          (p : MvPolynomial.homogeneousSubmodule (Option (Fin n)) A e)
          (z : G d), @SMul.smul _ _ modN.toSMul (p : MvPolynomial (Option (Fin n)) A)
            (z : ⨁ k : ℕ, generatorFiltration A b m k) ∈ G ((e : ℤ) + d)) ∧
        (∃ g : Fin r → generatorFiltration A b m 0,
          (∀ j : Fin r, (g j : M) = m j) ∧
          ∀ z : ⨁ d : ℕ, generatorFiltration A b m d,
            ∃ c : Fin r → MvPolynomial (Option (Fin n)) A,
              z = ∑ j, @SMul.smul _ _ modN.toSMul (c j)
                (DirectSum.of (fun k ↦ generatorFiltration A b m k) 0 (g j)))) ∧
      (IsDomain A → (∀ a : A, a ≠ 0 → Function.Injective (fun x : M ↦ a • x)) →
        ∀ a : A, a ≠ 0 → Function.Injective
          (fun z : ⨁ d : ℕ, generatorFiltration A b m d ↦ a • z)) := by
  sorry

end Module
