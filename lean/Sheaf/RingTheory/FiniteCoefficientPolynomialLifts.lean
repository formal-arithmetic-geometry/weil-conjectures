module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.TensorProduct.Defs

/-! # Simultaneous finite coefficient polynomial lifts

Source: Stacks Project, Tag 0367, proof of
`lemma-finite-type-local-source-fppf-algebra`, and Tag 034Y, final paragraph of
`lemma-descend-faithfully-flat-finite-presentation`
(blueprint: lem-a1-finite-coefficient-polynomial-lifts).
-/

@[expose] public section

set_option autoImplicit false

universe uR uC uA uD

open scoped TensorProduct BigOperators

namespace Algebra

/-- Simultaneously expand finitely many tensors and lift them through a polynomial algebra
on their coefficients over the relative integer model. The three given algebra structures
encode the arbitrary ring maps `R → A`, `C → A`, and `C → D`. The applied lambda installs
Mathlib's canonical right `C`-algebra structure on `R ⊗[ℤ] C`, without a local instance.

Source: Stacks Project, Tag 0367, finite coefficient enlargement in the proof of
`lemma-finite-type-local-source-fppf-algebra`; Tag 034Y, integer-model base extension
(blueprint: lem-a1-finite-coefficient-polynomial-lifts).

Proof:
1. Choose a finite presentation of `C` over `ℤ`; the images `c i` of its variables
   generate `C` (def-weil-pbc-finitely-presented-algebra, Stacks Tag 00F3).
2. Expand each `x j` as a finite sum of pure tensors, absorbing each `C`-scalar into
   the first factor (def-weil-pbc-module-tensor-product, Tags 00CV and 00CX).
   This gives `m j`, `a j k`, and `d j k`; empty sums are allowed.
3. The tensor pushout gives `τ(r ⊗ c) = ρ(r) * u(c)` over `ℤ`
   (lem-weil-pbc-algebra-tensor-pushout-universal-property).
   Write each `c` as an integer polynomial in the `c i`. Then `1 ⊗ c` is the same
   polynomial in the `1 ⊗ c i`. Finite pure-tensor expansions and
   `r ⊗ c = (r ⊗ 1) * (1 ⊗ c)` prove that these generate `R ⊗[ℤ] C` over `R`.
4. Polynomial evaluation gives `φ`, extending `τ` and taking `X ⟨j,k⟩` to `a j k`
   (def-weil-pbc-mv-polynomial-ring). Its constant values give both compatibilities.
5. Expand each polynomial in its variables, and then expand its coefficients using
   step 3. The images of `1 ⊗ c i` and all variables therefore generate the polynomial
   ring over `R`. Both generator families are finite, giving both finite-type claims
   (def-weil-pbc-finite-type-algebra).
6. The maps `p ↦ φ(p) ⊗ 1` and `d ↦ 1 ⊗ d` agree on `C` by step 4 and tensor
   balancing. The tensor pushout gives `λ(p ⊗ d) = φ(p) ⊗ d`. Apply additivity to
   the prescribed sum of `X ⟨j,k⟩ ⊗ d j k`, then use step 2. This also covers
   empty sums and `n = 0`, without any Noetherian or flatness assumption. -/
theorem exists_finite_coefficient_polynomial_lifts
    (R : Type uR) (C : Type uC) (A : Type uA) (D : Type uD)
    [CommRing R] [CommRing C] [CommRing A] [CommRing D]
    [Algebra R A] [Algebra C A] [Algebra C D] [FinitePresentation ℤ C]
    (n : ℕ) (x : Fin n → A ⊗[C] D) :
    (fun (_instCT : Algebra C (R ⊗[ℤ] C)) =>
      ∃ (m : Fin n → ℕ) (a : (j : Fin n) → Fin (m j) → A)
        (d : (j : Fin n) → Fin (m j) → D) (s : ℕ) (c : Fin s → C),
        (∀ j : Fin n, x j = ∑ k : Fin (m j), a j k ⊗ₜ[C] d j k) ∧
        Algebra.adjoin ℤ (Set.range c) = ⊤ ∧
        Algebra.adjoin R (Set.range (fun i : Fin s => (1 : R) ⊗ₜ[ℤ] c i)) = ⊤ ∧
        Algebra.adjoin R
          (Set.range (fun i : Fin s =>
            MvPolynomial.C (σ := ((j : Fin n) × Fin (m j))) ((1 : R) ⊗ₜ[ℤ] c i)) ∪
            Set.range MvPolynomial.X) = ⊤ ∧
        (algebraMap R (R ⊗[ℤ] C)).FiniteType ∧
        (algebraMap R (MvPolynomial ((j : Fin n) × Fin (m j)) (R ⊗[ℤ] C))).FiniteType ∧
        ∃ φ : MvPolynomial ((j : Fin n) × Fin (m j)) (R ⊗[ℤ] C) →+* A,
          φ.comp MvPolynomial.C =
            (Algebra.TensorProduct.productMap
              (algebraMap R A).toIntAlgHom (algebraMap C A).toIntAlgHom).toRingHom ∧
          (∀ j : Fin n, ∀ k : Fin (m j), φ (MvPolynomial.X ⟨j, k⟩) = a j k) ∧
          (∀ r : R, φ (MvPolynomial.C (r ⊗ₜ[ℤ] (1 : C))) = algebraMap R A r) ∧
          (∀ b : C, φ (MvPolynomial.C ((1 : R) ⊗ₜ[ℤ] b)) = algebraMap C A b) ∧
          ∃ l : (MvPolynomial ((j : Fin n) × Fin (m j)) (R ⊗[ℤ] C)) ⊗[C] D →+*
              A ⊗[C] D,
            (∀ (p : MvPolynomial ((j : Fin n) × Fin (m j)) (R ⊗[ℤ] C)) (b : D),
              l (p ⊗ₜ[C] b) = φ p ⊗ₜ[C] b) ∧
            ∀ j : Fin n,
              l (∑ k : Fin (m j), MvPolynomial.X ⟨j, k⟩ ⊗ₜ[C] d j k) = x j)
      (Algebra.TensorProduct.rightAlgebra (R := ℤ) (A := R) (B := C)) := by
  sorry

end Algebra
