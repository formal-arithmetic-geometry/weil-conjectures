/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W9
-/
module

public import Sheaf.Paper.AffineDiagonalIntegrationConstructions

/-! # Self-product base change of the presented integration transpose

Source: smooth-purity, Agreement on the model, trace comparison.
(blueprint: lem-pur-affine-diagonal-presented-base-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] affineDiagonalNormalCoordinates
  affineDiagonalNormalFunction affineDiagonalDifferenceLift
  Etale.FiniteSmoothPurity.ReesConeNormalized
  Etale.affineLinearCompactComparison
  Etale.affineLinearCoefficientDescent Etale.vectorIntegrationBaseCoefficientPullback

/-- The actual integration transposes commute with the self-product square in the
specified coordinate presentation. This asserts only the trace base-change equation;
it asserts neither invertibility nor restriction along the diagonal.
Source: smooth-purity, Agreement on the model, trace base change (Step 3 of
lem-pur-affine-diagonal-trace-restriction).
(blueprint: lem-pur-affine-diagonal-presented-base-change).

Proof: apply the ordered affine-space counit base-change equation to p:X→Y.
The Cartesian square of coordinate towers identifies its pullback bundle with
p₁:W→X by affineDiagonalProductCoordinates. Its top map is p₂, since both maps
preserve the ordered y-coordinates and the first base coordinate is x. Transport
the trace equation through affineLinearCompactComparison. Its proper/open and
bounded-below restriction comparisons identify the tower exchange with the
canonical compact-support exchange on the shifted Tate coefficient. Transport
the right objects through affineLinearCoefficientDescent and the normalized
root, tensor and even-shift pullback comparisons. Their composition laws give
exactly affineDiagonalTateRestriction. Take the exceptional adjunction transpose:
exchange naturality and the counit identity give the pullback of the original
transpose followed by the counit mate. That mate is precisely B, the specified
dualizingComplexBaseChangeMap for the flipped self-product square. Naturality
of the coordinate-isomorphism mate and the pullback compositor gives exactly
the presented transposes on both sides.
No inversion of a transpose, normal-cone construction, or diagonal restriction
is used here. The identity tower and empty schemes obey the same equations. -/
theorem affineDiagonalPresentedTranspose_selfBaseChange (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0) :
  let p := affineDiagonalProjection Y d
  let X := affineDiagonalSpace Y d
  let p₁ := pullback.fst p p
  let p₂ := pullback.snd p p
  let aX := p ≫ aY
  letI := affineDiagonalProjection_smooth Y d
  letI := SmoothOfRelativeDimension.smooth d p
  letI := Dnc.compactifiable P p aY
  letI := Dnc.compactifiable P p₁ aX
  letI := (P.comparedDiagonalBaseChange d p aX aY rfl).2.2.2.1
  let F := fun {U B : Scheme.{u}} (f : U ⟶ B) ↦
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor
  letI := (affineDiagonalProductCoordinates_spec Y d).1
  let B := Etale.dualizingComplexBaseChangeMap P.Coefficient
    (IsPullback.of_hasPullback p p).flip
  (P.affineDiagonalPresentedTranspose d p₁ aX r hA
        (asIso (affineDiagonalProductCoordinates Y d))
        (affineDiagonalProductCoordinates_spec Y d).2) =
      (P.affineDiagonalTateRestriction r hA p₂ aX d).inv ≫
        (F p₂).map
          (P.affineDiagonalPresentedTranspose d p aY r hA (Iso.refl X)
            (Category.id_comp p)) ≫ B := by sorry

end WeilConjectures.PurityFiniteSetting
