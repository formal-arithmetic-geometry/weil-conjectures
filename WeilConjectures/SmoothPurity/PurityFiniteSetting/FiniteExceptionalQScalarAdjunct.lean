/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalData
public import WeilConjectures.SixFunctors.PurCompactSupport.FiniteScalarPresentationCompatibility

/-! # Live finite exceptional comparison interface

The declarations below realize the live blueprint route, without the withdrawn
four-clause exceptional q-identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
variable (P : PurityFiniteSetting.{u}) (n m : ℕ) (h : m ≤ n)
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
/-- The finite-Tor clause of the live compact-support q-identification.
Source: blueprint finite reduction of purity, Step 2
(blueprint: lem-pur-finite-reduction-exceptional-q-identification).
Proof: the proper coefficient comparison satisfies the scalar-unit equation by
transposing under proper pullback/direct image and using compatibility of scalar
restriction with that adjunction. The open tensor comparison satisfies the same
unit equation by tensor-unit normalization. Paste these equations at the fixed
compactification: the actual proper/open comparison has inverse scalar transpose
rho composed with compact support of the scalar unit. Injectivity of the scalar
Hom bijection identifies that map with the scalar-adjunct comparison. The finite
q is the restriction of this actual proper/open map, so its full inclusion is the
same morphism. No counit-reduction or exceptional comparison equation is asserted.
All units used here exist for arbitrary quotients, including identity quotients,
zero objects and empty schemes. -/
theorem finiteExceptionalQ_scalarAdjunct
    (K : (FiniteExceptional.domain P.coefficients.l P.extension X n).FullSubcategory) :
    (FiniteExceptional.domain P.coefficients.l P.extension Y m).ι.map
      ((FiniteExceptional.q P.coefficients.l P.extension P.field
        P.coefficients.different f (@HasCompactification.compactification X Y f
        (hasCompactification_of_finiteType_over_field P.field.k X Y f)) h).hom.app K) =
      (P.finiteReductionSetting (n + 1) (Nat.succ_pos n)).finiteReductionCompactSupportComparison
        (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h) f K.obj := by
  let c := @HasCompactification.compactification X Y f
    (hasCompactification_of_finiteType_over_field P.field.k X Y f)
  let a := PurCompactSupport.finiteQuotientChange P.coefficients.l P.extension
    (n + 1) (m + 1) (Nat.succ_pos n) (Nat.succ_pos m) (Nat.succ_le_succ h)
  let φ := compactSupportLevelQuotient P.coefficients.l P.extension n m h
  have hc := PurCompactSupport.finiteScalarPresentationCompatibility
    P.coefficients.l P.extension P.extension n m a φ (fun T ↦ rfl) c
  have hc' := eq_of_heq hc
  have hq : (FiniteExceptional.domain P.coefficients.l P.extension Y m).ι.map
      ((FiniteExceptional.q P.coefficients.l P.extension P.field
        P.coefficients.different f c h).hom.app K) =
      (FiniteExceptional.supportMap P.coefficients.l P.extension f c h).app K.obj := by
    rfl
  rw [hq]
  dsimp only [FiniteExceptional.supportMap]
  rw [hc']
  change (Scheme.pbcDerivedExtend (Scheme.proEtaleConstantRingMap (T := Y) φ)).map
      ((PurCompactSupport.finiteImageIso P.coefficients.l P.extension n c).inv.app K.obj) ≫
    ((Functor.isoWhiskerRight
      (PurCompactSupport.finiteImageIso P.coefficients.l P.extension n c)
      (Scheme.pbcDerivedExtend (Scheme.proEtaleConstantRingMap (T := Y) φ))).hom ≫
      ExceptionalFiniteScalar.leftScalarMap φ c ≫
      (Functor.isoWhiskerLeft
        (Scheme.pbcDerivedExtend (Scheme.proEtaleConstantRingMap (T := X) φ))
        (PurCompactSupport.finiteImageIso P.coefficients.l P.extension m c).symm).hom).app
          K.obj ≫
    (PurCompactSupport.finiteImageIso P.coefficients.l P.extension m c).hom.app
      ((Scheme.pbcDerivedExtend (Scheme.proEtaleConstantRingMap (T := X) φ)).obj K.obj) = _
  dsimp only [PurCompactSupport.finite]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  change (Scheme.pbcDerivedExtend (Scheme.proEtaleConstantRingMap (T := Y) φ)).map
      (𝟙 _) ≫ (ExceptionalFiniteScalar.leftScalarMap φ c).app K.obj ≫ 𝟙 _ = _
  rw [(Scheme.pbcDerivedExtend (Scheme.proEtaleConstantRingMap (T := Y) φ)).map_id]
  simp only [Category.id_comp, Category.comp_id]
  change (ExceptionalFiniteScalar.leftScalarMap φ c).app K.obj =
    ((Scheme.pbcDerivedScalarAdjunction
      (Scheme.proEtaleConstantRingMap (T := Y) φ)).homEquiv _ _).symm
      ((Scheme.sfIntrinsicCompactSupport c
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).map
          ((Scheme.pbcDerivedScalarAdjunction
            (Scheme.proEtaleConstantRingMap (T := X) φ)).unit.app K.obj) ≫
        (Scheme.sfCompactSupportRestriction c φ).hom.app
          ((Scheme.pbcDerivedExtend (Scheme.proEtaleConstantRingMap (T := X) φ)).obj K.obj))
  apply ((Scheme.pbcDerivedScalarAdjunction
    (Scheme.proEtaleConstantRingMap (T := Y) φ)).homEquiv _ _).eq_symm_apply.mpr
  exact (unit_mateEquiv_symm
    (Scheme.pbcDerivedScalarAdjunction (Scheme.proEtaleConstantRingMap (T := X) φ))
    (Scheme.pbcDerivedScalarAdjunction (Scheme.proEtaleConstantRingMap (T := Y) φ))
    (TwoSquare.mk _ _ _ _ (Scheme.sfCompactSupportRestriction c φ).hom) K.obj).symm

end WeilConjectures.PurityFiniteSetting
