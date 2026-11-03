/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteAffineScalarCoordinates
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar

/-! # Source normalization of the supported affine scalar mate

Source: blueprint finite reduction of purity, Step 4.
(blueprint: lem-pur-affine-supported-source-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction

/-- The supported source scalar adjunct is the published compact-support comparison
followed by compact support of the published coefficient-unit map.
Source: blueprint Step 4, identification of the supported scalar unit
(blueprint: lem-pur-affine-supported-source-scalar).
Proof: transpose both maps through the native scalar adjunction. The compact-support
comparison is defined by compact support of that adjunction's unit followed by the
proper/open restriction comparison. For the closed zero section compact support is
exact direct image. Its exact-single comparison is natural in the coefficient map.
The native realization restriction square is identity on scalar sections and the
site restriction square preserves these same sections. The source scalar adjunct
therefore has the displayed ordinary supported coefficient map as its transpose.
On constant generators this is a mapped to its quotient, as prescribed by hη.
Constant-presheaf generators determine η uniquely. The coefficient unit comparison
has the same section formula, so scalar adjunction injectivity gives the equality.
This includes equal levels, level one, the empty scheme and ramified quotients. -/
theorem affineSupportedSource_scalar
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (S : Scheme.{u}) [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [IsSeparated (S ↘ Spec (.of P.field.k))]
    (η : Etale.ordinaryFiniteConstant P.Coefficient S ⟶
      (Sheaf.restrictScalars S.smallEtaleTopology (quotient P m hm hmn)).obj
        (Etale.ordinaryFiniteConstant (P.finiteReductionSetting m hm).Coefficient S))
    (hη : ∀ (W : S.Etaleᵒᵖ) (a : P.Coefficient),
      η.hom.app W ((toSheafify S.smallEtaleTopology ((Functor.const S.Etaleᵒᵖ).obj
        (ModuleCat.of P.Coefficient P.Coefficient))).app W a) =
      (toSheafify S.smallEtaleTopology ((Functor.const S.Etaleᵒᵖ).obj
        (ModuleCat.of (P.finiteReductionSetting m hm).Coefficient
          (P.finiteReductionSetting m hm).Coefficient))).app W (quotient P m hm hmn a)) :
    (P.finiteReduction m hm hmn (AffineSpace (ULift.{u} (Fin 1)) S)).map
        (affineSupportedSingleIso P S).hom ≫
      affineRealizeScalar P m hm hmn (AffineSpace (ULift.{u} (Fin 1)) S)
        (affineScalarSingle (quotient P m hm hmn) (AffineSpace (ULift.{u} (Fin 1)) S)
          (let ηT : affineOrdinarySupport P S ⟶
              (Sheaf.restrictScalars
                (AffineSpace (ULift.{u} (Fin 1)) S).smallEtaleTopology
                (quotient P m hm hmn)).obj
                ((Etale.lowerStar
                  (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient)
                  (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).obj
                  (Etale.ordinaryFiniteConstant
                    (P.finiteReductionSetting m hm).Coefficient S)) :=
            (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
              (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).map η ≫
              (AlgebraicGeometry.Etale.lowerStarCompRestrictScalarsIso
                (quotient P m hm hmn)
                (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).inv.app
                (Etale.ordinaryFiniteConstant
                  (P.finiteReductionSetting m hm).Coefficient S)
           ηT)) =
    P.finiteReductionCompactSupportComparison m hm hmn
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S) (P.coefficientUnit S) ≫
      ((P.finiteReductionSetting m hm).smoothCompactSupport
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).map
        (P.finiteReductionUnitComparison m hm hmn S) ≫
      (affineSupportedSingleIso (P.finiteReductionSetting m hm) S).hom := by
  sorry

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
