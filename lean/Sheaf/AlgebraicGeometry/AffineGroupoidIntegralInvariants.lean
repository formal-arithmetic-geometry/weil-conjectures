/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.AlgebraicGeometry.SchemeGroupoidLaws
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
import Mathlib.Topology.Sheaves.CommRingCat
import Sheaf.AlgebraicGeometry.AffineGroupoidInvariantRankStrata
import Sheaf.AlgebraicGeometry.AffineGroupoidPolynomialNormInvariant
import Sheaf.RingTheory.FiniteLocallyFreeNormCharacteristicPolynomial

/-!
# Integrality over the invariant ring of an affine groupoid

Source: Stacks Project, Groupoid Schemes, Lemma (Tag 03BJ)
(blueprint: lem-a1-affine-groupoid-integral-invariants).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An affine groupoid with finite locally free source and target is integral over
its invariant subring. The conclusion spells out a monic annihilator for each element.
Source: Stacks Project, `groupoids.tex`, Tag 03BJ, `lemma-integral-over-invariants`
(blueprint: lem-a1-affine-groupoid-integral-invariants).

Proof:
1. If `Spec A` is empty, `A` is the zero ring and the polynomial `X` annihilates its
   sole element. Otherwise, use `lem-a1-affine-groupoid-invariant-rank-strata` to
   decompose the groupoid into finitely many invariant affine clopen pieces of
   positive constant ranks `r`, with both projections finite locally free of rank `r`.
2. Apply `lem-weil-pbc-sheaf-disjoint-union-product` repeatedly to identify the rings
   of global sections with the finite products of the rings on these pieces.
   Source and target preserve the pieces, so their equalizer is the product of
   the corresponding equalizers `Cᵣ`; this uses only equality in a product.
3. On each piece and for the component `aᵣ` of `a`, apply
   `lem-a1-finite-locally-free-norm-characteristic-polynomial` to the source ring map
   and the target image of `aᵣ`. It gives the monic degree-`r` norm polynomial `Pᵣ`
   of `X - t♯(aᵣ)` and its Cayley--Hamilton annihilation equation in the arrow ring.
4. By `lem-a1-affine-groupoid-polynomial-norm-invariant` applied to `X - aᵣ`, all
   coefficients of `Pᵣ` lie in `Cᵣ`. This does not require globally free modules.
5. Equal source and target images of these coefficients identify the annihilation
   equation with `t♯(Pᵣ(aᵣ)) = 0`. Apply the identity section's ring map, a left
   inverse to `t♯`, to deduce `Pᵣ(aᵣ) = 0`.
6. Let `d` be the largest of the finitely many positive ranks. Multiply each `Pᵣ`
   by `X^(d-r)` to give them the same monic degree `d`. Combine their coefficients
   through the product equalizer from step 2. The resulting polynomial over the
   invariant subring is monic and vanishes at `a`, since it vanishes on every piece. -/
theorem isIntegral_affineGroupoid_invariants
    (A B : CommRingCat.{u}) (s t : Spec B ⟶ Spec A) (e : Spec A ⟶ Spec B)
    (i : Spec B ⟶ Spec B) (c : pullback s t ⟶ Spec B)
    (hG : Scheme.IsGroupoid s t e i c) [s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree] :
    ∀ a : A, ∃ P : Polynomial ((Spec.preimage s).hom.eqLocus (Spec.preimage t).hom),
      P.Monic ∧
        P.eval₂ ((Spec.preimage s).hom.eqLocus (Spec.preimage t).hom).subtype a = 0 := by
  sorry

end AlgebraicGeometry
