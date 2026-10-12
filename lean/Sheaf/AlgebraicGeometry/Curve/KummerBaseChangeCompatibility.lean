/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Authors: SHEAF group V1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Kummer
public import WeilConjectures.AlgebraicGeometry.Curve.Affine
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
public import Sheaf.AlgebraicGeometry.GmPicardPullback
public import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import Sheaf.AlgebraicGeometry.BaseChangeCurve
import Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility
import Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.AlgebraicGeometry.Curve.Brauer
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.Mathlib.Algebra.Module.Torsion.Basic
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Kummer compatibility under algebraically closed base change

Source: Weil conjectures blueprint, sec-curve-estimates/sk-prop-ext-invariance,
proper-case Kummer naturality sentence and affine-case Picard-torsion paragraph
(blueprint: lem-sc-kummer-base-change-compatibility).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

set_option autoImplicit false

/-- Kummer sequences, their connecting maps, and affine Picard torsion commute with extension of
algebraically closed ground fields. The proof follows the blueprint: base change preserves the
curve hypotheses; the comparison of units is adjoint to pullback; naturality of the derived
cohomology long exact sequence gives the ladder; degree zero is pullback of units and degree one
is pullback of invertible modules; in the affine case the Jacobian quotient and the abelian-variety
estimate give the isomorphism on `n`-torsion.

Source: Weil conjectures blueprint, sec-curve-estimates/sk-prop-ext-invariance, proper-case
Kummer naturality sentence and affine-case Picard-torsion paragraph
(blueprint: lem-sc-kummer-base-change-compatibility).

Proof: use `lem-sc-base-change-curve` for the hypotheses on the base change. The comparison map
of units and its restriction to roots of unity commute with the power maps, so the induced map of
short exact Kummer sequences is a `ShortComplex.Hom`. Apply `Sheaf.H.map_δSucc` and the
functoriality of the pullback maps to obtain the long-exact-sequence ladder. The degree-zero and
Picard assertions are the recorded pullback lemmas. For an affine curve, use the compactification
and Jacobian quotient from `lem-sc-pic-affine`, clauses (c) and (d) of `thm-av-final`, and
`lem-sc-divisible-quotient-torsion`.
-/
theorem kummer_base_change_compatibility
    (k k' : Type u) [Field k] [Field k'] [IsAlgClosed k] [IsAlgClosed k'] [Algebra k k']
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (P : Scheme.{u}) (π : P ⟶ C) (g : P ⟶ Spec (.of k'))
    (hπ : IsPullback π g f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (n : ℕ) [NeZero n] (hn : (n : k) ≠ 0) :
      ∃ (hC : (C.kummerSequence n).ShortExact)
        (hP : (P.kummerSequence n).ShortExact)
        (φ : ((Etale.upperStar AddCommGrpCat.{u + 1} π).mapShortComplex.obj
          (C.kummerSequence n)) ⟶ P.kummerSequence n),
        φ.τ₂ = upperStarGmSheafToGmSheaf π ∧
        φ.τ₃ = upperStarGmSheafToGmSheaf π ∧
        (∀ q : ℕ, ∀ x : Sheaf.H (C.kummerSequence n).X₃ q,
          Sheaf.H.map φ.τ₁ (q + 1)
              (Etale.cohomologyMap π (C.rootsOfUnitySheaf n) (q + 1)
                (Sheaf.H.δSucc hC q x)) =
            Sheaf.H.δSucc hP q
              (Sheaf.H.map φ.τ₃ q
                (Etale.cohomologyMap π C.gmSheaf q x))) ∧
        (∀ q : ℕ, ∀ x : Sheaf.H (C.kummerSequence n).X₁ q,
          Sheaf.H.map φ.τ₂ q
              (Etale.cohomologyMap π (C.kummerSequence n).X₂ q
                (Sheaf.H.map (C.kummerSequence n).f q x)) =
            Sheaf.H.map (P.kummerSequence n).f q
              (Sheaf.H.map φ.τ₁ q
                (Etale.cohomologyMap π (C.rootsOfUnitySheaf n) q x))) ∧
        (∀ q : ℕ, ∀ x : Sheaf.H (C.kummerSequence n).X₃ q,
          Sheaf.H.map φ.τ₃ q
              (Etale.cohomologyMap π C.gmSheaf q
                (Sheaf.H.map (C.kummerSequence n).g q x)) =
            Sheaf.H.map (P.kummerSequence n).g q
              (Sheaf.H.map φ.τ₂ q
                (Etale.cohomologyMap π C.gmSheaf q x))) ∧
        (∀ L : C.Pic,
          Pic.toCohomologicalPicardGroup P (Pic.map π L) =
            Sheaf.H.map (upperStarGmSheafToGmSheaf π) 1
              (Etale.cohomologyMap π C.gmSheaf 1
                (Pic.toCohomologicalPicardGroup C L))) ∧
        (∀ a : Γ(C, ⊤)ˣ,
          Sheaf.H.equiv₀ P.gmSheaf (MorphismProperty.Over.mkIdTerminal @Etale P)
            (Sheaf.H.map (upperStarGmSheafToGmSheaf π) 0
              (Etale.cohomologyMap π C.gmSheaf 0
                ((Sheaf.H.equiv₀ C.gmSheaf
                  (MorphismProperty.Over.mkIdTerminal @Etale C)).symm
                    (ULift.up (Additive.ofMul a))))) =
            ULift.up (Additive.ofMul (Units.map π.appTop.hom.toMonoidHom a))) ∧
        (IsAffine C →
          ∃ F : {x : C.Pic // x ^ n = 1} → {x : P.Pic // x ^ n = 1},
            Function.Bijective F ∧ ∀ x, (F x).1 = Pic.map π x.1)
      := by
  sorry

end AlgebraicGeometry
