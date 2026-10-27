/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H8
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientData
public import Sheaf.Paper.SixFunctorDatum
import Sheaf.Paper.FiniteRingCompactSupportProjection
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Sheaf.SixFunctors.OpenTensorNormalization

/-! # Invertibility of projection under constant-coefficient presentation

Source: the presentation comparison in the proof of prop-sf-pf-reduction;
Stacks Tags 07A4, 07A6 and 0GL1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport
/-- The finite-ring compact-support projection theorem in normalized intrinsic tensor
coordinates. This is a single-level invertibility statement: it asserts no scalar
square or equivalence between two reduction levels.
Source: prop-sf-pf-reduction, finite projection paragraph; Stacks 0F0G, 07A4,
07A6, 0GL1 (blueprint: lem-sf-finite-projection-presentation).

Proof: the coefficient ring is finite and killed by a positive power of l.
Bounded constructibility gives lower and upper bounds for nonzero cohomology.
Give the compactification's middle scheme its structure map r followed by the
structure map of Y. Properness of r makes this middle scheme separated and of
finite type over the finite-field base. The compactification relation gives the
over-base condition for j. Apply `isIso_finiteRingCompactSupportProjection`.

To identify its map, restriction to constant scalar sections is an exact
equivalence inverse to the specified intrinsic realization. The direct-image
comparison is identity on sections. Its adjoint pullback comparison preserves
the geometric counit. The tensor comparison sends each balanced pure tensor to
the same two sections. Apply these comparisons to flat K-flat representatives
and signed total tensors, then descend through resolving-class localization.
Transpose the proper projection: both coordinates become the tensor comparison
followed by counit tensor identity. For the open factor transpose its inverse:
both coordinates give the open unit followed by inverse tensor comparison.
Adjunction injectivity identifies both pieces. Paste them with the canonical
pullback compositor. The resulting endpoint isomorphisms conjugate the known
finite-ring map to the displayed normalized map, so invertibility transfers.
This applies equally to empty schemes, zero inputs and identity immersions. -/
theorem finiteProjectionPresentation_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ)
    (X Y : WeilConjectures.SixFunctorSpace D)
    [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left] (c : Compactification f.hom.left)
    (aX : ProEtaleTensorModel X.obj.left (proEtaleConstantRing X.obj.left
      (Padic.coefficientExtensionRing C.l E (n + 1))))
    (aZ : ProEtaleTensorModel c.Z (proEtaleConstantRing c.Z
      (Padic.coefficientExtensionRing C.l E (n + 1))))
    (aY : ProEtaleTensorModel Y.obj.left (proEtaleConstantRing Y.obj.left
      (Padic.coefficientExtensionRing C.l E (n + 1))))
    (K : proEtaleDerivedCategory X.obj.left
      (Padic.coefficientExtensionRing C.l E (n + 1)))
    (L : proEtaleDerivedCategory Y.obj.left
      (Padic.coefficientExtensionRing C.l E (n + 1)))
    (hK : WeilConjectures.finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n)
      X.obj.left K)
    (hL : WeilConjectures.finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n)
      Y.obj.left L) :
    IsIso (((projectionMap (finite C.l E (n + 1) (Nat.succ_pos n)) c aX aZ aY
      (proEtaleConstantRingCompositeCoefficients_eq c.i c.g
        (Padic.coefficientExtensionRing C.l E (n + 1))).symm).app K).app L) := by sorry

end WeilConjectures.PurCompactSupport
