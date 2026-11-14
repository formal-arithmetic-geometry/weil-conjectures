/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientSourcePullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarPullbackComparison

/-! # Supported-source normalization of the scalar/pullback mate
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] derivedUpper derivedScalars singlePullback
  scalarPullbackComparison

/-- Supported coefficient endpoints commute with geometric inverse image under the
scalar mate. The coefficient change is arbitrary; no positive line or diagonal class
occurs in the equation, and no diagram or trace compatibility is assumed. -/
theorem diagonalSupported_pullbackScalarNormalization
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (L₀ : ∀ X : Scheme.{u}, Modules R X) (L : ∀ X : Scheme.{u}, Modules T X)
    (m₀P : (upperStar Ab.{u + 1} (baseP g)).obj (L₀ (ProjectiveLine Y)).X ⟶
      (L₀ (ProjectiveLine Y')).X)
    (m₀W : (upperStar Ab.{u + 1} (baseW g)).obj (L₀ (diagonalSurface Y)).X ⟶
      (L₀ (diagonalSurface Y')).X)
    (mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X)
    (mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X)
    (s₀ : SourcePullback R g L₀ m₀P m₀W) (s : SourcePullback T g L mP mW)
    (c : Endpoint a (Mod.regular (condensedRingObj R (ProjectiveLine Y)))
      (Mod.regular (condensedRingObj T (ProjectiveLine Y)))
      (coefficientMap a (ProjectiveLine Y)))
    (c' : Endpoint a (Mod.regular (condensedRingObj R (ProjectiveLine Y')))
      (Mod.regular (condensedRingObj T (ProjectiveLine Y')))
      (coefficientMap a (ProjectiveLine Y')))
    (e : Endpoint a (source R Y) (source T Y) (supportMap a Y c.semilinear.hom).hom)
    (e' : Endpoint a (source R Y') (source T Y') (supportMap a Y' c'.semilinear.hom).hom) :
    (scalarPullbackComparison a (baseW g)).app
        ((DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).obj (source R Y)) ≫
      (derivedUpper T (baseW g)).map e.iso.hom ≫
      (singlePullback T (baseW g) (source T Y)).hom ≫
      (DerivedCategory.singleFunctor (Modules T (diagonalSurface Y')) 0).map s.supported.hom =
    (derivedScalars a (diagonalSurface Y')).map
      ((singlePullback R (baseW g) (source R Y)).hom ≫
        (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map
          s₀.supported.hom) ≫ e'.iso.hom := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
