/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularProjectionClass

/-! # Coordinate charts for the specified regular comparison

Source: sk-thm-regular.proof.md, Step 4(i)--(iii).
(blueprint: lem-pur-regular-comparison-coordinate-charts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- A coordinate chart comparing a supported morphism with contraction along an
oriented affine projection. This records no Kummer equality or sign calculation.
Source: sk-thm-regular.proof.md, Step 4(i)--(iii)
(blueprint: lem-pur-regular-comparison-coordinate-charts). -/
structure RegularComparisonCoordinateChart
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [NeZero (ringChar Λ)]
    {X Z : Scheme.{u}} [HasInvertibleExponent Λ X]
    (c : ℕ) (i : Z ⟶ X) [IsRegularImmersion c i]
    (φ : constantComplex Λ Z ⟶
      (R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) where
  frame : i.EtaleFrame c
  open_frame : IsOpenImmersion frame.e
  base : Scheme.{u}
  [noetherianBase : IsNoetherian base]
  [exponentSpace : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin c); base)]
  orientation : dualizingComplex Λ (𝔸(ULift.{u} (Fin c); base) ↘ base) ≅
    (tateObject Λ 𝔸(ULift.{u} (Fin c); base) c)⟦2 * (c : ℤ)⟧
  normalized : regularProjectionOrientationNormalized Λ base c orientation
  coordinateMap : frame.U ⟶ 𝔸(ULift.{u} (Fin c); base)
  [etale_coordinateMap : Etale coordinateMap]
  equations : ∀ j, coordinateMap.appTop (AffineSpace.coord base (ULift.up j)) = frame.f j
  supportMap : frame.U.zeroLocusSubscheme (Set.range frame.f) ⟶
    𝔸(ULift.{u} (Fin c); base).zeroLocusSubscheme
      (Set.range (fun j : Fin c ↦ AffineSpace.coord base (ULift.up j)))
  square : IsPullback supportMap (frame.U.zeroLocusSubschemeι (Set.range frame.f))
    (𝔸(ULift.{u} (Fin c); base).zeroLocusSubschemeι
      (Set.range (fun j : Fin c ↦ AffineSpace.coord base (ULift.up j)))) coordinateMap
  comparison : frameRestriction Λ frame
      ((supportedClassMapEquiv Λ i ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)).symm φ) =
    restrictSupportedClass Λ coordinateMap
      (𝔸(ULift.{u} (Fin c); base).zeroLocusSubschemeι
        (Set.range (fun j : Fin c ↦ AffineSpace.coord base (ULift.up j))))
      (frame.U.zeroLocusSubschemeι (Set.range frame.f)) supportMap square
      (leftDerivedUpperStarConstantComplexIso Λ coordinateMap).inv
      (leftDerivedUpperStarTateShiftIso Λ coordinateMap c)
      (regularProjectionSupportedClass Λ base c orientation)

attribute [instance] RegularComparisonCoordinateChart.noetherianBase
  RegularComparisonCoordinateChart.exponentSpace
  RegularComparisonCoordinateChart.etale_coordinateMap

end AlgebraicGeometry.Etale
