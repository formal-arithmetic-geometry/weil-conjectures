/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteAffineScalarCoordinates

/-! # Target normalization of the supported affine scalar mate

Source: blueprint finite reduction of purity, Step 4.
(blueprint: lem-pur-affine-supported-target-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction

/-- The scalar adjunct of a root-generator-normalized line map is the specified
intrinsic affine input comparison, including its degree-two shift.
Source: blueprint Step 4, identification of the root-line scalar unit
(blueprint: lem-pur-affine-supported-target-scalar).
Proof: the root-kernel equation determines q uniquely as the power M/N map.
Choose a primitive ell^n-root in the algebraically closed base and use its power
as the ell^m-root. The generator equation for θ identifies its ordinary scalar
adjunct with the corresponding map between these free rank-one root charts.
The site/scalar comparison and the native scalar presentation are the adjoint
mates of restriction squares that preserve sections, so the realization has the
same scalar-unit formula in these charts. The exact-derived shift comparisons
are compatible with these mates. Thus the realized shifted adjunct followed by
the smaller input chart is the reduced larger input chart, the scalar shift map,
and the shifted coefficient-unit comparison. This is the defining chart equation
for finiteReductionOrientationInputComparison, which determines it uniquely.
The same argument works for equal levels and empty schemes; no quotient flatness
or ramification-index divisibility is used. -/
theorem affineSupportedTarget_scalar
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (S : Scheme.{u}) [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [IsSeparated (S ↘ Spec (.of P.field.k))]
    (q : (AffineSpace (ULift.{u} (Fin 1)) S).rootsOfUnitySheaf P.diagonalExponent ⟶
      (AffineSpace (ULift.{u} (Fin 1)) S).rootsOfUnitySheaf
        (P.finiteReductionSetting m hm).diagonalExponent)
    (hq : q ≫ kernel.ι ((P.finiteReductionSetting m hm).diagonalExponent •
        𝟙 (AffineSpace (ULift.{u} (Fin 1)) S).gmSheaf) =
      (P.diagonalExponent / (P.finiteReductionSetting m hm).diagonalExponent) •
        kernel.ι (P.diagonalExponent • 𝟙 (AffineSpace (ULift.{u} (Fin 1)) S).gmSheaf))
    (θ : Scheme.finiteEtaleTateLine (AffineSpace (ULift.{u} (Fin 1)) S)
        P.diagonalExponent P.Coefficient P.diagonalExponent_annihilates ⟶
      (Sheaf.restrictScalars (AffineSpace (ULift.{u} (Fin 1)) S).smallEtaleTopology
        (quotient P m hm hmn)).obj
        (Scheme.finiteEtaleTateLine (AffineSpace (ULift.{u} (Fin 1)) S)
          (P.finiteReductionSetting m hm).diagonalExponent
          (P.finiteReductionSetting m hm).Coefficient
          (P.finiteReductionSetting m hm).diagonalExponent_annihilates))
    (hθ : ∀ (W : (AffineSpace (ULift.{u} (Fin 1)) S).Etaleᵒᵖ) (a : P.Coefficient)
      (z : ((AffineSpace (ULift.{u} (Fin 1)) S).rootsOfUnitySheaf
        P.diagonalExponent).obj.obj W),
      θ.hom.app W (Scheme.finiteEtaleTateOneGenerator P.Coefficient P.diagonalExponent
        (AffineSpace (ULift.{u} (Fin 1)) S) P.diagonalExponent_annihilates W a z) =
      Scheme.finiteEtaleTateOneGenerator (P.finiteReductionSetting m hm).Coefficient
        (P.finiteReductionSetting m hm).diagonalExponent (AffineSpace (ULift.{u} (Fin 1)) S)
        (P.finiteReductionSetting m hm).diagonalExponent_annihilates W
        (quotient P m hm hmn a) (q.hom.app W z)) :
    affineRealizeScalar P m hm hmn (AffineSpace (ULift.{u} (Fin 1)) S)
      (affineScalarShiftedSingle (quotient P m hm hmn)
        (AffineSpace (ULift.{u} (Fin 1)) S) θ) =
      (P.finiteReductionOrientationInputComparison m hm hmn S).hom := by
  sorry

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
