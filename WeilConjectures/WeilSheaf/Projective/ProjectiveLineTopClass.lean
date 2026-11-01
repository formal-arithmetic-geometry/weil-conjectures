/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Projective.ProjectiveLineRestriction
public import WeilConjectures.WeilSheaf.TateTwist
import WeilConjectures.WeilSheaf.Projective.ProjectiveChernPullbackAction
import WeilConjectures.WeilSheaf.Projective.ProjectiveChernAdjunctTop
import WeilConjectures.AlgebraicGeometry.NativeCartier.NativeCartierClass
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-! # The degree-two projective-line class in the native Weil category

Source: thm-amb-p1-decomposition and the coefficient passage in
lem-pur-b3-weil-projective-decomposition, steps 1--3.
(blueprint: lem-pur-h3-projective-top-class).
-/

@[expose] public section

universe u
open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]

/-- The Chern summand gives the top cohomology isomorphism on Weil sheaves.
(blueprint: lem-pur-h3-projective-top-class).

Source: latest blueprint, thm-amb-p1-decomposition.proof.md, the Kummer generator;
lem-pur-b3-weil-projective-decomposition, steps 1--3, coefficient passage.

Proof: construct the Kummer first Chern class of O(1) with finite torsion coefficients,
use the inverse Tate line and evaluation to untwist it, and transpose along q^* ⊣ Rq_*.
Tensoring with an input complex and the proper projection formula give the transformation.
The finite-level classes commute with reduction, so applying derived inverse limit to
integral constructible models, then inverting the uniformizer and extending through the
finite coefficient fields, gives the same transformation with algebraic-closure coefficients.
Carry this construction out for equivariant complexes, using the root pullback maps in
the Tate line: the Kummer boundary and every adjunction map are Frobenius compatible.
Thus the resulting maps live in the native derived category of Weil sheaves. Their shift
compatibility follows from that of tensor, the even shift [-2], and the adjunction.
On an input sheaf M, the degree-two map is the tensor product of M with the degree-one
Kummer generator on each geometric projective line. The finite projective-line theorem
makes this map invertible. Proper base change and conservativity of geometric stalks,
followed by the compatible coefficient passage, give invertibility on M. This assertion
only computes the degree-two map; it does not assert vanishing in other degrees, a
biproduct decomposition, or normalization at infinity. The right-adjoint shift structure
is any structure compatible with the fixed pullback and adjunction; adjoint uniqueness
makes that structure unique. -/
theorem exists_projectiveLine_top_class
    [(derivedLowerStar (k₀ := k₀) (l := l) (ProjectiveLine X ↘ X)).CommShift ℤ]
    [(upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l)
      (ProjectiveLine X ↘ X)).CommShift ℤ] :
    ∃ c : tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ) ⟶
        projectiveLineCohomology (k₀ := k₀) (l := l) X,
      NatTrans.CommShift c ℤ ∧ ∀ M : WeilSheaf k₀ l X,
        IsIso ((homologySheaf 2).map (c.app (WeilSheaf.toComplex.obj M))) := by
  obtain ⟨C⟩ := ProEtale.NativeCartier.native_cartier_class k₀ l
    (Ne.symm (Fact.out : ringChar k₀ ≠ l))
  obtain ⟨a, ha, hnorm⟩ := exists_projectiveChern_pullback_action X C
  let T := tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ)
  let L := upperStar (k₀ := k₀) (l := l) (ProjectiveLine X ↘ X)
  let R := derivedLowerStar (k₀ := k₀) (l := l) (ProjectiveLine X ↘ X)
  let adj := upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l)
    (ProjectiveLine X ↘ X)
  let c : T ⟶ L ⋙ R :=
    (Functor.rightUnitor T).inv ≫ Functor.whiskerLeft T adj.unit ≫
      (Functor.associator T L R).inv ≫ Functor.whiskerRight a R
  have hc (K : WeilComplex k₀ l X) :
      c.app K = adj.homEquiv _ _ (a.app K) := by
    simp [c, Adjunction.homEquiv_unit, T, L, R]
  let : NatTrans.CommShift a ℤ := ha
  refine ⟨c, NatTrans.CommShift.of_homEquiv adj a c hc, fun M ↦ ?_⟩
  rw [hc]
  exact projectiveChern_adjunct_top_isIso X C M _ (hnorm M)

end AlgebraicGeometry.WeilComplex
