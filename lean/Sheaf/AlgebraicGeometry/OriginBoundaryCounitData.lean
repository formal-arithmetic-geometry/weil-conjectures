/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module
public import Sheaf.AlgebraicGeometry.OriginComparisonArrows

/-!
Geometric parts of the origin comparison.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Step 2, and sk-prop-an Step 5(d).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
/-- Normalized boundaries and the actual extension-by-zero counit square.
Source: Stacks 03PL, 0A45, 03S3 and 015F
(blueprint: lem-pur-origin-boundary-counit-data). -/
structure OriginBoundaryCounitData (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) where
  hX : IsUnit (N : Γ(AffineSpace PUnit.{u + 1} S, ⊤))
  hP : IsUnit (N : Γ(ProjectiveLine S, ⊤))
  hIX : (AffineSpace.zeroSection PUnit.{u + 1} S).ker.IsInvertible
  hIP : (ProjectiveLine.infinity S).ker.IsInvertible
  transport : OrdinaryFiniteTwistTransport A N hA
  restriction : (upperStar (ModuleCat.{u + 1} A) (ProjectiveLine.infinityChart S)).obj
    (originProjectiveSheaf A S) ≅ originAffineSheaf A S
  affineClass : Ext (originAffineSheaf A S)
    (Scheme.finiteEtaleTateLine (AffineSpace PUnit.{u + 1} S) N A hA) 2
  projectiveClass : Ext (originProjectiveSheaf A S)
    (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA) 2
  restriction_normalization : restriction.hom = originRestrictionExchange A S
  affine_boundary : SupportedKummerBoundary A N hA
    (AffineSpace.zeroSection PUnit.{u + 1} S) hIX hX affineClass
  projective_boundary : SupportedKummerBoundary A N hA
    (ProjectiveLine.infinity S) hIP hP projectiveClass
  counit_iso : IsIso (originSupportCounit A S restriction)
  counit_square : (originOpenExtension A S).map
      (originBoundaryArrow A N hA (AffineSpace PUnit.{u + 1} S) _ affineClass) ≫
      originTwistCounit A N hA transport S hP =
    originSupportCounit A S restriction ≫
      originBoundaryArrow A N hA (ProjectiveLine S) _ projectiveClass

/-- Construct the Cartier boundary pair and its actual counit compatibility.
Source: rank-one Thom Step 2; Stacks 03PL, 0A45, 03S3 and 015F
(blueprint: lem-pur-origin-boundary-counit-data).
Proof: invertibility of N pulls back from the field. The zero sections in the smooth
relative curves are Cartier. Take their unique normalized supported Kummer boundaries
and the roots/pure-tensor normalized twist transport. The identity-over-point square is
Cartesian; finite base change makes its supported constant exchange invertible.
Boundary pullback gives the corresponding Ext square. To pass to the actual counits,
prove naturality of Ext for a natural transformation to the identity by dimension
shifting against an injective embedding. Apply it to the open adjunction counit;
exact-single and shift comparisons identify its derived realization with the stated
square. Finite-open comparison in the identity-over-point square makes the sheaf counit
invertible; the exact-single realization preserves this property. The argument also
works for the zero coefficient ring and N=1. -/
theorem origin_boundary_counit_data (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (N : ℕ) (hN : 0 < N) (hΩ : IsUnit (N : Ω))
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    Nonempty (OriginBoundaryCounitData A N hA (Spec (.of Ω))) := by sorry

end AlgebraicGeometry.Etale
