/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.CategoryTheory.LeftExactUpperTruncationComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # The canonical affine derived edge after upper truncation

Source: Stacks Project, Tags 0AVW and 08D4, with bound N = 1.
(blueprint: lem-sc-affine-algebra-upper-truncation-edge).
-/

@[expose] public section
set_option autoImplicit false

universe v wX wY
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Direct image preserves finite limits, since underlying sections are evaluated on
inverse-image opens. Source: Stacks Project, Tag 079V.
(blueprint: lem-sc-affine-algebra-upper-truncation-edge). -/
theorem affineAlgebraDirectImage_preservesFiniteLimits
    {X Y : Scheme.{v}} (f : X ⟶ Y) :
    PreservesFiniteLimits (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)) := by
  let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  let U := SheafOfModules.forget (moduleRings (directImageAlgebraSpace f))
  let V := PresheafOfModules.toPresheaf (moduleRings (directImageAlgebraSpace f)).obj
  have : PreservesFiniteLimits (F ⋙ U ⋙ V) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.toPresheaf (moduleRings X.toRingedSpace).obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj (TopologicalSpace.Opens.map f.base).op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves F (U ⋙ V)

noncomputable instance affineAlgebraDirectImage_preservesFiniteLimits_inst
    {X Y : Scheme.{v}} (f : X ⟶ Y) :
    PreservesFiniteLimits (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)) :=
  affineAlgebraDirectImage_preservesFiniteLimits f

/-- The derived upper-truncation edge is an isomorphism and sends the canonical image
of a cycle to its original homology-sheaf class. K-injectivity is not assumed here.
Source: Stacks Project, Tag 0AVW, cohomology display and its omitted detail;
Tag 08D4 (2) and (3), N = 1, and Tag 05TC.
(blueprint: lem-sc-affine-algebra-upper-truncation-edge).

Proof: Put A = tau<=n I and B = tau>=n A. The lower tail tau<=n-1 I has
quasi-coherent cohomology. On inverse images of affine opens, affine vanishing and
the bound of Tag 08D4 with N=1 give zero derived sections of this tail in degrees
n and n+1. Its truncation triangle therefore makes H^n(RGamma(A)) -> H^n(RGamma(B))
invertible. B is canonically H^n(I) placed in degree n; bottom derived cohomology
is ordinary sections, by left exactness and the degree-zero derived comparison.
The resulting restriction-compatible, scalar-linear edge maps glue to the displayed
isomorphism over f_*O_X. For its formula use the natural comparison from raw sections
to derived sections in the square A -> B. In degree n this map is the quotient of
cycles by boundaries. The raw truncation inclusion A -> I is invertible on degree-n
homology under the left exact direct-image functor. Its inverse, the canonical
cokernel-to-homology isomorphism, and the comparison unit are exactly the factors in
upperTruncationBoundaryComparison. Thus the naturality square gives the asserted
identity after the cokernel projection. No K-injectivity or boundedness of I is used.
Empty affine opens, the zero complex, and every integer degree are included. -/
theorem affine_algebra_upper_truncation_edge
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wX} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))]
    [EnoughInjectives (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    (hI : ∀ n : ℤ, (I.homology n).IsQuasicoherent) (n : ℤ) :
    let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
    ∃ e : (DerivedCategory.homologyFunctor
        (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) n).obj
        (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj (I.truncLE n))) ≅
        F.obj (I.sc n).homologyData.left.H,
      cokernel.π (F.map (I.sc n).homologyData.left.f') ≫
          F.upperTruncationBoundaryComparison I n ≫ e.hom =
        F.map (I.sc n).homologyData.left.π := by sorry

end AlgebraicGeometry
