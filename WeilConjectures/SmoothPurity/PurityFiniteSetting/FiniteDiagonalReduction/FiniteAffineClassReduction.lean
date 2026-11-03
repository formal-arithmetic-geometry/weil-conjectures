/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionAffineOrientation
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteAffineSupportedSourceScalar
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteAffineSupportedTargetScalar
import WeilConjectures.AlgebraicGeometry.FiniteSupportedScalarModulus
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteScalarExtSquare
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback

/-! # Reduction of the intrinsic supported affine class

Source: blueprint finite reduction of purity, Step 4.
(blueprint: lem-pur-affine-supported-class-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

set_option maxHeartbeats 1600000 in
-- Kernel checking the scalar, support and realization composites exceeds the default budget.
/-- The intrinsic supported class satisfies the reduced scalar square.
Source: blueprint Step 4, the normalized supported Cartier boundary.
(blueprint: lem-pur-affine-supported-class-reduction).
Proof: transfer the ordinary supported Kummer reduction equation through the
source and target scalar adjunct comparisons. The coefficient unit and root map
are sectionwise normalized, so the ordinary scalar Ext square is exactly the
intrinsic class equation. The exact comparison and realization functors preserve
Yoneda composition and the shifted degree-two map. -/
theorem affineSupportedClassReduction
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (S : Scheme.{u}) [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [IsSeparated (S ↘ Spec (.of P.field.k))]
    :
      (P.finiteReduction m hm hmn (AffineSpace (ULift.{u} (Fin 1)) S)).map
        ((P.smoothCompactSupport (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).map
          (P.finiteReductionOrientation S) ≫
            P.smoothExceptionalCounit (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
              (P.finiteReductionOrientationInput S)) ≫
        (P.finiteReductionOrientationInputComparison m hm hmn S).hom =
      P.finiteReductionCompactSupportComparison m hm hmn
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S) (P.coefficientUnit S) ≫
        ((P.finiteReductionSetting m hm).smoothCompactSupport
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).map
          (P.finiteReductionUnitComparison m hm hmn S) ≫
        ((P.finiteReductionSetting m hm).smoothCompactSupport
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).map
          ((P.finiteReductionSetting m hm).finiteReductionOrientation S) ≫
        (P.finiteReductionSetting m hm).smoothExceptionalCounit
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
          ((P.finiteReductionSetting m hm).finiteReductionOrientationInput S) := by
  let Q := P.finiteReductionSetting m hm
  let T := AffineSpace (ULift.{u} (Fin 1)) S
  let i := AffineSpace.zeroSection (ULift.{u} (Fin 1)) S
  let φ := quotient P m hm hmn
  have hdiv : Q.diagonalExponent ∣ P.diagonalExponent :=
    pow_dvd_pow P.coefficients.l hmn
  have hQn : (P.diagonalExponent : Q.Coefficient) = 0 :=
    (ringChar.spec Q.Coefficient P.diagonalExponent).mpr
      (dvd_trans ((ringChar.spec Q.Coefficient Q.diagonalExponent).mp
        Q.diagonalExponent_annihilates) hdiv)
  have hn : 0 < P.diagonalExponent := pow_pos (Fact.out : P.coefficients.l.Prime).pos _
  have hm' : 0 < Q.diagonalExponent := pow_pos (Fact.out : P.coefficients.l.Prime).pos _
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hexp⟩ :=
    (Scheme.finiteEtaleTwistPullbackData Q.Coefficient Q.diagonalExponent
      hm' Q.diagonalExponent_annihilates).laws
  obtain ⟨q, t, hq, ht, _⟩ := hexp P.diagonalExponent hn hdiv T
    (P.diagonalExponent_isUnit (T ↘ Spec (.of P.field.k)))
  let c := (P.existsUnique_finiteReductionOrientationClass S).choose
  let c' := (Q.existsUnique_finiteReductionOrientationClass S).choose
  obtain ⟨η, θ, hη, hθ, hunit, hsquare⟩ := Etale.supportedKummerScalarModulus
    φ P.diagonalExponent Q.diagonalExponent hn hm' hdiv
    P.diagonalExponent_annihilates hQn Q.diagonalExponent_annihilates i
    (finiteReductionZeroCartier S)
    (P.diagonalExponent_isUnit (T ↘ Spec (.of P.field.k)))
    (Q.diagonalExponent_isUnit (T ↘ Spec (.of Q.field.k))) q (t 1) hq ht c c'
    (P.existsUnique_finiteReductionOrientationClass S).choose_spec.1
    (Q.existsUnique_finiteReductionOrientationClass S).choose_spec.1
  let ηT := (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).map η ≫
    (Etale.lowerStarCompRestrictScalarsIso φ i).inv.app
      (Etale.ordinaryFiniteConstant Q.Coefficient S)
  have hηT : ηT = (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).map η := by
    dsimp only [ηT, Etale.lowerStarCompRestrictScalarsIso, Iso.refl_inv,
      NatTrans.id_app, Functor.comp_obj]
    exact Category.comp_id _
  have ho := affineScalarSquare_of_extSquare φ T ηT θ
    (by rw [hηT]; exact hunit) c c' (by rw [hηT]; exact hsquare)
  have hsource := affineSupportedSource_scalar P m hm hmn S η hη
  have htarget := affineSupportedTarget_scalar P m hm hmn S q hq θ hθ
  let V := affineOrdinaryRealization P T
  let W := affineOrdinaryRealization Q T
  let R := P.finiteReduction m hm hmn T
  let σ := affineNativeOrdinaryComparison P m hm hmn T
  have hnat := σ.hom.naturality c.hom
  change R.map (V.map c.hom) ≫ σ.hom.app _ =
    σ.hom.app _ ≫ W.map ((Etale.FiniteSmoothPurity.ordinaryScalar φ T).map c.hom) at hnat
  have hreal : R.map (V.map c.hom) ≫
      affineRealizeScalar P m hm hmn T (affineScalarShiftedSingle φ T θ) =
    affineRealizeScalar P m hm hmn T
      (affineScalarSingle φ T ηT) ≫
      W.map c'.hom := by
    dsimp only [affineRealizeScalar]
    rw [← Category.assoc, hnat, Category.assoc, ← W.map_comp, ho, W.map_comp]
    simp only [σ, W, V, Q, T, i, Category.assoc]
  rw [affineOrientation_counit P S, affineOrientation_counit Q S,
    affineSupportedSingle_class P S, affineSupportedSingle_class Q S]
  simp only [Functor.map_comp, Category.assoc]
  rw [← htarget, hreal, reassoc_of% hsource]

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
