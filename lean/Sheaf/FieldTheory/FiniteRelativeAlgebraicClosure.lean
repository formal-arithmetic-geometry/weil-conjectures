/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-!
# Finiteness of the relative algebraic closure

Source: Stacks Project, Fields, Lemma Tag 037J
(lemma-algebraic-closure-in-finitely-generated)
(blueprint: lem-zl-finite-algebraic-closure).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped IntermediateField.algebraAdjoinAdjoin

private theorem linearIndependent_adjoin_of_algebraicIndependent
    {k E K ι κ : Type*} [Field k] [Field E] [Field K]
    [Algebra k E] [Algebra k K] [Algebra E K] [IsScalarTower k E K]
    {x : ι → K} (hx : AlgebraicIndependent E x) {b : κ → E}
    (hb : LinearIndependent k b) :
    LinearIndependent (IntermediateField.adjoin k (Set.range x))
      (algebraMap E K ∘ b) := by
  classical
  -- Expand a polynomial-coefficient relation, then compare each monomial coefficient.
  have hxk := hx.restrictScalars (algebraMap k E).injective
  suffices h : LinearIndependent (Algebra.adjoin k (Set.range x))
      (algebraMap E K ∘ b) by
    exact h.localization (IntermediateField.adjoin k (Set.range x))
      (nonZeroDivisors (Algebra.adjoin k (Set.range x)))
  rw [linearIndependent_iff']
  intro s c hc i hi
  let p (j : κ) : MvPolynomial ι k := hxk.repr (c j)
  have heval (q : MvPolynomial ι k) :
      MvPolynomial.aeval x (MvPolynomial.map (algebraMap k E) q) =
        (MvPolynomial.aeval x : MvPolynomial ι k →ₐ[k] K) q := by
    simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_map,
      IsScalarTower.algebraMap_eq k E K]
  have hq : ∑ j ∈ s, MvPolynomial.C (b j) *
      MvPolynomial.map (algebraMap k E) (p j) = 0 := by
    apply hx.eq_zero_of_aeval_eq_zero
    simpa only [map_sum, map_mul, MvPolynomial.aeval_C, heval,
      p, hxk.aeval_repr, Function.comp_apply, Algebra.smul_def,
      Subalgebra.algebraMap_apply, mul_comm] using hc
  have hcoeff (d : ι →₀ ℕ) : ∀ j ∈ s, (p j).coeff d = 0 := by
    apply linearIndependent_iff'.mp hb s
    have h := congrArg (MvPolynomial.coeff d) hq
    simpa only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_map, MvPolynomial.coeff_zero, Algebra.smul_def, mul_comm] using h
  have hp : p i = 0 := by
    ext d
    simpa only [MvPolynomial.coeff_zero] using hcoeff d i hi
  apply Subtype.ext
  have h := congrArg (MvPolynomial.aeval x : MvPolynomial ι k →ₐ[k] K) hp
  simpa only [p, hxk.aeval_repr, map_zero, Subalgebra.coe_zero] using h

namespace algebraicClosure

/-- The algebraic closure of the base field inside a finitely generated field extension
is finite-dimensional over the base field.
Source: Stacks Project, Fields, Lemma Tag 037J
(lemma-algebraic-closure-in-finitely-generated)
(blueprint: lem-zl-finite-algebraic-closure).

Proof outline:
1. Choose finitely many field generators of K/k and, by
   `lem-weil-pbc-finitely-generated-field-finite-transcendence-basis`, a finite
   transcendence basis x_1,...,x_r. Put L = k(x_1,...,x_r). The generators of K/k
   are algebraic over L and still generate K over L. Thus
   `lem-weil-pbc-algebraic-generators-finite-extension` gives n = [K:L] finite.
2. Let k' be any finite intermediate field of K/k and put m = [k':k]. Each element
   of k' is algebraic over k by linear dependence of its first m+1 powers.
   By `lem-zl-independence-algebraic-base`, the x_i remain independent over k'.
   Induct on j with F_j = k(x_1,...,x_j) and E_j = k'(x_1,...,x_j).
   Initially [E_0:F_0] = m. Independence makes x_(j+1) transcendental over E_j:
   clearing the finitely many coefficient denominators in any alleged polynomial
   relation would contradict independence over k'. Evaluation identifies the two
   rational-function extensions with F_(j+1) and E_(j+1), compatibly with inclusion
   (`def-weil-rational-function-field`). Then `lem-zl-rational-function-degree`
   gives [E_(j+1):F_(j+1)] = [E_j:F_j] = m.
3. The inclusion k'(x_1,...,x_r) into K preserves L-linear independence.
   Hence [k':k] = [k'(x_1,...,x_r):L] <= [K:L] = n.
4. Put A = algebraicClosure k K (`def-weil-relative-algebraic-closure`). The degrees
   of its finite intermediate fields lie in the nonempty finite set {1,...,n}.
   Choose one k' of maximal degree m. A k-basis of k' also generates it as a field.
   For any alpha in A, the basis and alpha are algebraic over k, so
   `lem-weil-pbc-algebraic-generators-finite-extension` makes k'(alpha)/k finite.
   Its degree is at most m by maximality and at least m by inclusion. Equal finite
   dimensions force k'(alpha) = k'. Thus every alpha belongs to k', so A = k'
   and A/k is finite. -/
theorem finite_of_fg (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG) : Module.Finite k (algebraicClosure k K) := by
  classical
  -- Work over the field generated by a transcendence basis.
  have : Algebra.EssFiniteType k K := IntermediateField.fg_top_iff.mp hfg
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  let x : s → K := Subtype.val
  let L := IntermediateField.adjoin k (Set.range x)
  have : Algebra.IsAlgebraic L K := hs.isAlgebraic_field
  have : Algebra.EssFiniteType L K := Algebra.EssFiniteType.of_comp k L K
  have : Module.Finite L K := Algebra.finite_of_essFiniteType_of_isAlgebraic
  -- The constants' basis stays independent, so finite dimension forces its index to be finite.
  let b := Module.Free.chooseBasis k (algebraicClosure k K)
  have hb : LinearIndependent L ((algebraMap (algebraicClosure k K) K) ∘ b) :=
    linearIndependent_adjoin_of_algebraicIndependent hs.1.algebraicClosure b.linearIndependent
  have : Finite (Module.Free.ChooseBasisIndex k (algebraicClosure k K)) := hb.finite
  exact Module.Finite.of_basis b

end algebraicClosure
