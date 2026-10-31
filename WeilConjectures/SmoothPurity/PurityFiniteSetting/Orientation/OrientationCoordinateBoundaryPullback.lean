/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientationData

import WeilConjectures.SmoothPurity.PurityFiniteSetting.Orientation.OrientationCoordinateModelBoundary

/-! # Geometric pullback in the Gysin coordinate chart

Source: blueprint affine-line orientation, geometric-fibre sentence; Milne, Section 9
(blueprint: lem-pur-orientation-coordinate-boundary-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] CoordinateKummerPullback CoordinateBoundarySiteAgreement
  SupportHomSquareCoherent SupportHomPair.Transport.derivedMap supportHomDerivedComparison
  coordinateEtaleCoefficientPullback

/-- The actual coordinate support boundary pulls back to the fibre coordinate boundary,
for any two snake-normalized Gysin charts. This is an equality of support classes,
independent of a global orientation morphism or any residue isomorphism.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-a1-kummer/thm-pur-affine-line-orientation.proof.md, geometric-fibre sentence;
Milne, Section 9, functoriality of cohomology with supports
(blueprint: lem-pur-orientation-coordinate-boundary-pullback).

Proof: Apply coordinate_boundary_geometric_pullback to obtain its normalized models
and transport p. The pro-etale coefficient-compatible clause gives equality of the two
model boundaries. orientation_coordinate_model_boundary identifies both chart boundaries
with these model boundaries, and the coefficient transport is definitionally the
orientationSupportRestriction map. Rewrite y followed by a using hy. -/
theorem orientation_coordinate_boundary_pullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (D : OrientationSupportData P h Y)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra P.field.k Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y)
    (hy : y ≫ a = Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω)))
    (D' : OrientationSupportData P h (Spec (CommRingCat.of Ω))) :
    ∃ p : proEtaleSupportHomTransport P (zeroSection Y)
        (zeroSection (Spec (CommRingCat.of Ω))) (AffineSpace.map (ULift.{u} (Fin 1)) y),
      P.orientationSupportRestriction h y p (D.coordinateBoundary P h a) =
        D'.coordinateBoundary P h
          (Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))) := by
  classical
  let hs := coordinate_boundary_geometric_pullback P h Y a
  let M := hs.choose
  let ht := hs.choose_spec Ω y
  let M' := ht.choose
  let he := ht.choose_spec
  let hp := he.choose_spec
  let p := hp.choose
  have hmodel : P.orientationSupportRestriction h y p (M.alphaPro P h a) =
      M'.alphaPro P h (y ≫ a) :=
    hp.choose_spec.choose_spec.choose_spec.2.1.2.1
  refine ⟨p, ?_⟩
  exact (congrArg (P.orientationSupportRestriction h y p)
    (P.orientation_coordinate_model_boundary h Y a D M)).trans
      (hmodel.trans (by
        rw [hy]
        exact (P.orientation_coordinate_model_boundary h _ _ D' M').symm))

end WeilConjectures.PurityFiniteSetting
