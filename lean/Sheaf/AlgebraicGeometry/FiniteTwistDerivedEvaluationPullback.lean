/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps

/-! # Pullback of the normalized shifted finite-line evaluation

Source: Stacks Tags 03PK and 03Q1, and the evaluation identification in
thm-amb-p1-decomposition.proof.md
(blueprint: lem-asd-finite-twist-derived-evaluation-pullback).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- The canonical shifted evaluation and right unit commute with inverse image.
The first equation is the evaluation-pairing square; the second is its tensor-unit
normalization. These concern any scheme morphism and do not involve a projective-line
splitting, direct image, properness, or finite coefficients.
Source: etaleFiniteTwistPullback, negative evaluation and derived tensor clauses;
main-20261015, thm-amb-p1-decomposition.proof.md, evaluation identifications
(blueprint: lem-asd-finite-twist-derived-evaluation-pullback).

Proof: in degree zero use the negative-normalization equation of the normalized
finite-twist transport, with n=0. Its degree-zero comparison is compatible with the
flat single-object tensor comparison because both are induced by the same tensor
of complexes before localization. Move the symmetry past inverse image using
its braided tensor comparison. Normalized positive transport agrees with t by
ordinaryFiniteTwistTransport_unique. Apply the shift comparison to the two factors,
with shifts -2 and 2, and use compatibility of the inverse-image tensor comparison
with derivedTensorShiftIso. Their sum is zero; shift-zero coherence removes the
remaining shift, giving the first equation. The even shifts give sign +1. For the
second equation identify the constant object with the monoidal unit via
singleFunctorObjUnitIso, identify its pullback comparison with the canonical
monoidal unit comparison, and apply right unitality of the oplax monoidal inverse
image. Naturality of singleFunctorObjUnitIso converts this back to the displayed
right-unit maps. All identifications are canonical, including for N=1, zero
coefficients, and empty schemes. -/
theorem finiteTwistDerivedEvaluation_pullback
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    ((ordinaryFinitePullback A f).map (p1DecompositionEvaluation A N hN hA Y hY) ≫
      (ordinaryFiniteUnitPullback A f).hom =
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app
        (p1DecompositionTwist A N hA Y (-1) (-2))).app
          ((ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧) ≫
        ((ordinaryFiniteTensor A X).obj
          ((ordinaryFinitePullback A f).obj (p1DecompositionTwist A N hA Y (-1) (-2)))).map
            (ordinaryFiniteShiftedLinePullback A N hA t f hY).hom ≫
        ((ordinaryFiniteTensor A X).map
          (p1DecompositionTwistPullback A N hN hA f hY (-1) (-2)).hom).app _ ≫
        p1DecompositionEvaluation A N hN hA X
          ((map_natCast f.appTop.hom N) ▸ hY.map f.appTop.hom)) ∧
    (∀ K : DerivedCategoryModule A Y,
      (ordinaryFinitePullback A f).map (derivedTensorSingleUnitIso K).inv ≫
        ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app K).app
          (ordinaryFiniteUnit A Y) ≫
        ((ordinaryFiniteTensor A X).obj ((ordinaryFinitePullback A f).obj K)).map
          (ordinaryFiniteUnitPullback A f).hom =
      (derivedTensorSingleUnitIso ((ordinaryFinitePullback A f).obj K)).inv) := by sorry

end AlgebraicGeometry.Etale
