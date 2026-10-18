/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Finiteness of the relative algebraic closure

Source: Stacks Project, Fields, Lemma Tag 037J
(lemma-algebraic-closure-in-finitely-generated)
(blueprint: lem-zl-finite-algebraic-closure).
-/

@[expose] public section

set_option autoImplicit false

universe u v

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
  sorry

end algebraicClosure
