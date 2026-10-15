/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Finite affine morphisms and finite covers by closed sections

Source: Stacks Project, Morphisms, Tag 03HW, Lemma `lemma-massage-finite`, clauses (1)–(5)
(blueprint: lem-weil-pbc-finite-affine-section-cover).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite morphism to an affine scheme admits, after surjective finite locally free base
change, a closed immersion into an affine finite locally free scheme covered by finitely many
closed sections. Source: Stacks Project, Morphisms, Tag 03HW, clauses (1)–(5)
(blueprint: lem-weil-pbc-finite-affine-section-cover).

Proof plan:
1. For empty `X`, take identity maps and the single closed subscheme `X`. Otherwise write
   `X = Spec A`, `Y = Spec B`, choose finite module generators of `B`, and choose monic
   positive-degree equations for them using finite-algebra integrality
   (`lem-weil-pbc-finite-algebra-is-integral`).
2. Successively split these equations over nonzero finite free extensions and multiply their
   bases to obtain a finite free extension `A'` of `A`
   (`lem-weil-pbc-monic-finite-free-splitting-extension`, `def-weil-pbc-free-module`).
3. The extension is injective by uniqueness of basis coefficients. Integral lying over gives
   surjectivity on spectra; the finite-free spectrum lemma gives finite local freeness
   (`lem-weil-pbc-integral-injective-lying-over`, `lem-weil-pbc-finite-free-algebra-spectrum`).
4. Form `C = A'[T₁,...,Tₙ]/(P₁(T₁),...,Pₙ(Tₙ))`. Iterated monic quotients give its finite
   monomial basis, hence `W = Spec C` is finite locally free over `X' = Spec A'`
   (`lem-weil-pbc-monic-quotient-free`, `lem-weil-pbc-finite-free-algebra-spectrum`).
5. Sending the variables to the base-changed generators gives a surjection to `A' ⊗[A] B`,
   hence the closed immersion of the actual pullback over `X'`
   (`lem-weil-pbc-fibre-product-affine-spectra`,
   `lem-weil-pbc-closed-immersion-affine-cover-criterion`,
   `def-weil-pbc-module-tensor-product`).
6. Evaluation at each tuple of roots gives a quotient isomorphic to `A'`. These define closed
   sections; every prime contains one linear factor of every `Pᵢ`, so their images cover `W`.
   This also treats repeated roots and the single empty tuple when there are no generators.
7. Base change of the basis gives the same finite basis over `B`; apply the finite-free
   spectrum lemma. For nonzero `B`, basis coefficients give injectivity and lying over gives
   surjectivity; for zero `B` both spectra are empty
   (`lem-weil-pbc-free-module-base-change-free`). No Noetherian assumption is used. -/
theorem exists_finite_affine_section_cover {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [IsAffine X] :
    ∃ (X' : Scheme.{u}) (a : X' ⟶ X),
      IsAffine X' ∧ Surjective a ∧ a.IsFiniteLocallyFree ∧
      ∃ (W : Scheme.{u}) (p : W ⟶ X') (j : pullback f a ⟶ W),
        IsAffine W ∧ p.IsFiniteLocallyFree ∧ IsClosedImmersion j ∧
        j ≫ p = pullback.snd f a ∧
        (∃ (n : ℕ) (Z : Fin n → Scheme.{u}) (i : ∀ k : Fin n, Z k ⟶ W),
          (∀ k : Fin n, IsClosedImmersion (i k) ∧ IsIso (i k ≫ p)) ∧
          ∀ w : W, ∃ (k : Fin n) (z : Z k), i k z = w) ∧
        Surjective (pullback.fst f a) ∧ (pullback.fst f a).IsFiniteLocallyFree := by
  sorry

end AlgebraicGeometry
