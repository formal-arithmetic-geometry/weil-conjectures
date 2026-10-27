/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import Sheaf.Paper.TwistedCoordinateSectionProjective

/-! The projective part of coordinate-section normalization. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
open AffineLinePurity VectorIntegrationSite

/-- The projective coordinate divisor has line bundle O(1), and the actual affine
supported class forgets, after the open counit and the identity-normalized section
comparison, to its positive Chern adjunct.

Source: current blueprint, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, rank-one paragraph;
lem-pur-twisted-coordinate-section-normalization, Steps 1--3.
(blueprint: lem-pur-coordinate-section-projective-trace).

Proof: On D(T1), the divisor is t=0, with ideal frame t; on D(T0) it is empty,
with ideal frame 1. The dual frames t^-1 and 1 have the transition of O(1).
The supported Kummer theorem identifies the class of this divisor with the
positive Chern class after forgetting support, and identifies its restriction
with the affine supported class by Cartier-preserving pullback. Apply the
open-closed exact sequence to the projective supported constant sheaf. Its
restriction to infinity is zero, so the open counit identifies its extension
from the affine chart with that projective sheaf. Naturality of this same
counit compares the two supported arrows. Apply Rq_* and precompose with the
inverse section-composition comparison. The composite inverse-image/direct-image
adjunction for qs=id carries its unit to identity, so this source comparison
is exactly the identity-normalized one in sectionComposition. The resulting
map is the Chern adjunct, giving the displayed equation for every allowed b.
No flatness of the coefficient ring is used: flatness belongs to the root line.
For the empty base the categories are zero and the same equations hold. -/
theorem coordinateSectionProjectiveTrace
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    [IsNoetherian T] [IsClosedImmersion (projectiveZero T)] :
    ProjectiveNormalization P T ∧
    ∀ (b : ℕ) (hA : ((P.coefficients.l ^ (b + 1) : ℕ) : Ring P) = 0)
      (hT : IsUnit ((P.coefficients.l ^ (b + 1) : ℕ) : Γ(T, ⊤)))
      (hI : (sectionMap T).ker.IsInvertible),
    ((sectionComposition (Ring P) T).inv.app (Etale.ordinaryFiniteUnit (Ring P) T) ≫
      (compact (Ring P) T).map
        (restrictedSupported (Ring P) T (P.coefficients.l ^ (b + 1))
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hT hI) ≫
    (Etale.ordinaryFinitePushforward (Ring P) (ProjectiveLine T ↘ T)).map
      ((Etale.affineTraceOpenAdjunction (Ring P) T).counit.app
        ((Etale.ordinaryFiniteLine (Ring P) (P.coefficients.l ^ (b + 1)) hA
          (ProjectiveLine T))⟦(2 : ℤ)⟧)) =
      Etale.ordinaryFiniteP1ChernPushforward (Ring P) (P.coefficients.l ^ (b + 1)) hA T
        (Etale.projectiveLineTraceDatum (P.coefficients.l ^ (b + 1))
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (Ring P) hA T hT).chern) := by sorry

end AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
