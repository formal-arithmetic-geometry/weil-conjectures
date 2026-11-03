/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityConventions.PurityConventions
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameClass
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceZeroSectionPurity
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteExceptionalComposition
public import WeilConjectures.SixFunctors.AdicSmoothDualizing.AdicSmoothDualizingFinitePowers
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection

/-! # Regular closed immersion purity: coordinate target comparisons

Split from `Sheaf.Paper.RegularClosedImmersionPurity` (compile-time split; same declarations,
names and statements; the original module re-exports this one). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor
namespace WeilConjectures.RegularClosedImmersionPurity

set_option maxHeartbeats 800000 in
-- The published root-tensor comparison unfolds several derived-site layers.
/-- Compare the coordinate construction's higher-exponent shifted line with the
frame line through their common inverse-limit root tensor, using the two
canonical root-projection comparisons, with exact single and shift identifications.
Source: clause (b), zero-section normalization (blueprint: sk-thm-regular). -/
def coordinateLineMap (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) :
    AffineSpacePurity.shiftedLine (AffineZeroPurity.setting P n) X ⟶
      input (AffineZeroPurity.setting P n) X 1 :=
  (VectorIntegrationSite.twistDerived P.coefficients.l P.extension n X
    (AffineLinePurity.primeUnit (AffineZeroPurity.setting P n) X aX)
    (n + 1) (AffineSpacePurity.annihilates (AffineZeroPurity.setting P n)) 1 2).hom ≫
    (VectorIntegrationSite.twistDerived P.coefficients.l P.extension n X
      (AffineLinePurity.primeUnit (AffineZeroPurity.setting P n) X aX)
      n (AffineZeroPurity.setting P n).diagonalExponent_annihilates 1 2).inv ≫
    (targetComparison (AffineZeroPurity.setting P n) X 2 1).hom

/-- The successor step of `coordinateTargetMap`: append the root-normalized line to a
comparison in exponent `c`, using the published right-shift-first tensor comparison and
frame multiplication. Factored out so the kernel checks this composite once.
Source: clause (b), zero-section normalization (blueprint: sk-thm-regular). -/
def coordinateTargetMapStep (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ)
    (φ : AffineZeroPurity.target P n X c ⟶ input (AffineZeroPurity.setting P n) X c) :
    AffineZeroPurity.target P n X (c + 1) ⟶ input (AffineZeroPurity.setting P n) X (c + 1) :=
  let Q := AffineZeroPurity.setting P n
  let T := @curriedTensor (CupDerivedCategory Q X) _ (cupMonoidal Q X)
  (T.map φ).app _ ≫
    (T.obj (input Q X c)).map (coordinateLineMap P n X aX) ≫
    (cupTensorShiftIso ((cupSingle Q X).obj (Q.frameTwist X c))
      ((cupSingle Q X).obj (Q.frameTwist X 1)) (2 * (c : ℤ)) 2).hom ≫
    (shiftFunctor _ (2 * (c : ℤ) + 2)).map (Q.frameTensorNext X c) ≫
    (eqToIso (congrArg (fun j : ℤ ↦
      ((cupSingle Q X).obj (Q.frameTwist X (c + 1)))⟦j⟧)
      (PurityFiniteSetting.frameDegreeNext c))).hom

/-- Canonical ordered comparison of the coordinate target with A(c)[2c].
It starts with the zero-shift unit and appends the root-normalized line, using
exactly the published right-shift-first tensor comparison and frame multiplication.
Source: clause (b), zero-section normalization (blueprint: sk-thm-regular). -/
def coordinateTargetMap (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) :
    (c : ℕ) → AffineZeroPurity.target P n X c ⟶
      input (AffineZeroPurity.setting P n) X c
  | 0 => (shiftFunctorZero _ ℤ).inv.app _
  | c + 1 => coordinateTargetMapStep P n X aX c (coordinateTargetMap P n X aX c)

end WeilConjectures.RegularClosedImmersionPurity
