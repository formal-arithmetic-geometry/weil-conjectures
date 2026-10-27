/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.Depth
import WeilConjectures.RingTheory.DepthInSES
import WeilConjectures.RingTheory.DepthLeSupportDimension

/-!
# Punctual acyclicity over a regular local ring

Source: Stacks Project, Algebra, Tag 00N0, lemma-acyclic, specialized to finite free
modules; Mumford, Abelian Varieties, III §13, printed p.127
(blueprint: lem-sfb-regular-local-punctual-acyclicity).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A finite free complex in degrees zero through the dimension of a regular local
ring, whose cohomology localizes to zero at every nonmaximal prime, has zero
cohomology below that dimension.
Source: Stacks Project, Algebra, Tag 00N0, lemma-acyclic; Mumford, Abelian Varieties,
III §13, printed p.127 (blueprint: lem-sfb-regular-local-punctual-acyclicity).

Proof:
1. Set C_i = F^i / im(d^{i-1}) and D_i = im(C_i → F^{i+1}). The complex identity
   identifies the kernel of C_i → D_i with H^i(F). Thus
   0 → H^i(F) → C_i → D_i → 0 is short exact. The terms C_i and D_i are finite,
   and H^i(F) is finite by lem-trf-noetherian-submodule-finitely-presented.
2. Choose d generators of the maximal ideal. They form a regular sequence by
   lem-weil-pbc-regular-local-generators-regular-sequence. On each nonzero finite
   free F^j, multiplication on successive quotients is injective coordinatewise,
   and the final quotient is a nonzero finite power of the residue field. Hence
   depth(F^j) ≥ d by def-weil-pbc-depth and def-weil-pbc-regular-sequence.
   For a zero term the depth is infinity, so this inequality still holds.
3. Negative cohomology vanishes because the complex terms there vanish. This
   finishes d = 0. Otherwise induct on 0 ≤ i ≤ d with depth(C_i) ≥ d - i and
   H^j(F) = 0 for 0 ≤ j < i. The base is C_0 = F^0.
4. If i < d and H^i(F) is nonzero, the depth lemma
   lem-weil-pbc-depth-in-ses gives depth(H^i(F)) ≥ 1 from the short exact sequence
   in step 1; if D_i = 0 this follows directly from H^i(F) ≅ C_i. Its support is
   contained in the maximal ideal by hypothesis, and therefore has dimension
   at most zero. The bound lem-weil-pbc-depth-le-support-dimension contradicts
   positive depth. Thus H^i(F) = 0.
5. Now 0 → C_i → F^{i+1} → C_{i+1} → 0 is short exact. The depth lemma gives
   depth(C_{i+1}) ≥ min(d, d - i - 1) = d - i - 1. If C_i is zero this is the
   free-term bound; if C_{i+1} is zero it has infinite depth. If F^{i+1} is zero,
   both other terms are zero. This proves the induction step in all cases.
6. Induction gives H^i(F) = 0 for 0 ≤ i < d; combine with step 3 for all i < d.
-/
theorem isZero_homology_lt_dimension_of_punctual_support
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (hbounded : ∀ i : ℤ, i < 0 ∨ (d : ℤ) < i → IsZero (F.X i))
    (hfree : ∀ i : ℤ, Module.Free R (F.X i) ∧ Module.Finite R (F.X i))
    (hsupport : ∀ (p : Ideal R) [p.IsPrime], p ≠ IsLocalRing.maximalIdeal R →
      ∀ i : ℤ, Subsingleton (LocalizedModule p.primeCompl (F.homology i))) :
    ∀ i : ℤ, i < (d : ℤ) → IsZero (F.homology i) := by
  sorry

end CochainComplex
