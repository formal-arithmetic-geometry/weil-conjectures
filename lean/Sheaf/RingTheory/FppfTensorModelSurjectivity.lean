module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.FiniteType

/-!
# Surjectivity from a faithfully flat tensor model

Source: Stacks Project, Descent, Tag 0367, proof of
`lemma-finite-type-local-source-fppf-algebra`, final paragraph
(blueprint: lem-a1-fppf-tensor-model-surjectivity).
-/

@[expose] public section

universe uR uC uP uA uD uB

open scoped TensorProduct

namespace Algebra

/-- The canonical model map `P ⊗[C] D → B`, sending `p ⊗ d` to `f(φ(p)) * g(d)`.
Source: Stacks Project, Descent, Tag 0367, final paragraph of the proof of
`lemma-finite-type-local-source-fppf-algebra`
(blueprint: lem-a1-fppf-tensor-model-surjectivity). -/
def fppfTensorModelMap
    (C : Type uC) (P : Type uP) (A : Type uA) (D : Type uD) (B : Type uB)
    [CommRing C] [CommRing P] [CommRing A] [CommRing D] [CommRing B]
    [Algebra C P] [Algebra P A] [Algebra C A] [IsScalarTower C P A]
    [Algebra A B] [Algebra C B] [IsScalarTower C A B]
    [Algebra C D] [Algebra D B] [IsScalarTower C D B] :
    P ⊗[C] D →ₐ[C] B :=
  TensorProduct.productMap
    ((IsScalarTower.toAlgHom C A B).comp (IsScalarTower.toAlgHom C P A))
    (IsScalarTower.toAlgHom C D B)

/-- Lifts of the finite `R`-algebra generators in a faithfully flat tensor model give
surjectivity of its source map, the specified tensor comparison, and generators of the quotient.
Source: Stacks Project, Descent, Tag 0367, final paragraph of the proof of
`lemma-finite-type-local-source-fppf-algebra`
(blueprint: lem-a1-fppf-tensor-model-surjectivity).

Proof:
1. The tensor pushout universal property gives `fppfTensorModelMap`. It respects the
   `R`-structure. Express any element of `B` as a polynomial in the `b j`, and evaluate
   that polynomial at the lifts `z j`. Its image is the given element, proving surjectivity
   (lem-weil-pbc-algebra-tensor-pushout-universal-property,
   def-weil-pbc-finite-type-algebra).
2. Faithful flatness of `C → D` is preserved by base change to `P`, giving faithful
   flatness of `P → P ⊗[C] D` (lem-weil-pbc-faithfully-flat-base-change).
3. Compose `TensorProduct.cancelBaseChange C P A A D` with `e`. The cancellation
   formulas give the displayed formula and inverse formula. On pure tensors its value
   at `1 ⊗ z` is the model map; additivity gives this for every `z`
   (lem-weil-pbc-tensor-cancel-base-change, def-weil-pbc-module-tensor-product).
4. The composite of `φ ⊗ id_D` with `e` is the surjective model map. Thus `φ ⊗ id_D`
   is surjective. Swap tensor factors and reflect exactness of `P → A → 0` along the
   faithfully flat `C`-module `D`; this says `φ` is surjective
   (lem-weil-pbc-module-tensor-comm, def-weil-pbc-faithfully-flat-ring-map).
5. Lift any element of `A` to `P`, express it as a polynomial in the specified `p i`,
   and apply `φ`. Hence the `φ(p i)` generate `A` over `R`
   (def-weil-pbc-finite-type-algebra). -/
theorem fppfTensorModelSurjectivity
    (R : Type uR) (C : Type uC) (P : Type uP) (A : Type uA)
    (D : Type uD) (B : Type uB)
    [CommRing R] [CommRing C] [CommRing P] [CommRing A] [CommRing D] [CommRing B]
    [Algebra R P] [Algebra P A] [Algebra R A] [IsScalarTower R P A]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra C P] [Algebra C A] [IsScalarTower C P A]
    [Algebra C B] [IsScalarTower C A B]
    [Algebra C D] [Algebra D B] [IsScalarTower C D B]
    [Module.FaithfullyFlat C D]
    (e : A ⊗[C] D ≃ₐ[A] B)
    (he : ∀ (a : A) (d : D),
      e (a ⊗ₜ[C] d) = algebraMap A B a * algebraMap D B d)
    (n : ℕ) (b : Fin n → B) (hb : Algebra.adjoin R (Set.range b) = ⊤)
    (z : Fin n → P ⊗[C] D)
    (hz : ∀ j : Fin n, fppfTensorModelMap C P A D B (z j) = b j) :
    Module.FaithfullyFlat P (P ⊗[C] D) ∧
    Function.Surjective (fppfTensorModelMap C P A D B) ∧
    (∃ θ : A ⊗[P] (P ⊗[C] D) ≃ₐ[A] B,
      (∀ (a : A) (p : P) (d : D),
        θ (a ⊗ₜ[P] (p ⊗ₜ[C] d)) = e ((a * algebraMap P A p) ⊗ₜ[C] d)) ∧
      (∀ (a : A) (d : D), θ.symm (e (a ⊗ₜ[C] d)) = a ⊗ₜ[P] (1 ⊗ₜ[C] d)) ∧
      (∀ w : P ⊗[C] D, θ (1 ⊗ₜ[P] w) = fppfTensorModelMap C P A D B w)) ∧
    Function.Surjective (algebraMap P A) ∧
    (∀ (N : ℕ) (p : Fin N → P), Algebra.adjoin R (Set.range p) = ⊤ →
      Algebra.adjoin R (Set.range (fun i : Fin N ↦ algebraMap P A (p i))) = ⊤) := by
  sorry

end Algebra
