/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurIntegralTower.PurStrictIntegralExchangeData

/-! # Quotient units and ordinary open normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The quotient reconstruction units for isomorphism pullback are invertible on
these complete inputs, and ordinary open exchange is the inverse open-unit mate.

Source: constituent compatibility in the proof of
prop-pur-weil-equivariance-compatibilities, strict integral normalization steps 1,
5--8 (blueprint: lem-pur-integral-geometric-input-normalization).

Proof: the completed coefficient identifications along an isomorphism identify
ordinary pullback with exact site reindexing. It commutes with the entire quotient
diagram and its augmentation, since on flat-term representatives both routes send
a tensor to its relabeling with the same quotient scalar. Thus it preserves the
quotient-complete objects and ordinaryToCompleted is invertible on them. Open
extension preserves completeness by completedOpenExchangeComparison; proper direct
image preserves it by directImageRlimIso and the projection-unit equation. Apply
these facts to K, j!K and Rp*j!K. For the last equality transpose the inverse
ordinary open exchange under j'! ⊣ j' inverse image. The transported open adjunction
and pullback compositor preserve the open unit. Its transpose is exactly the
pulled open unit followed by cbcSquarePull inverse, the definition of cbcBetaInv.
Injectivity of transposition and uniqueness of inverses identify the forward map
with cbcBeta. This uses no derived evaluation faithfulness or finite-origin inputs.
The argument also applies to zero objects, empty schemes and an empty ideal tuple. -/
theorem purIntegralGeometricInputNormalization
    (P : WeilConjectures.PurityFiniteSetting.{t}) :
  ∀ {X' X Y' Y : Scheme.{t}} [X.Over
      (Spec (.of P.field.k))]
      [Y.Over
      (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      {f : X ⟶ Y} [f.IsOver
      (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X} [IsIso g] [IsIso g']
      (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z) [IsIso gb]
      (sp : ChosenCartesianSquare gb c'.g c.g g)
      (sj : OpenImmersionSquare g' c'.i c.i gb)
      (r : ℕ) (a : Fin r → PbcIntegralRing P.coefficients.l P.extension)
      (ha : Ideal.span (Set.range a) = (pbcIntegralDatum P.coefficients.l P.extension).ideal)
      (K : (cbcCompleteProperty (pbcIntegralDatum P.coefficients.l P.extension)
        X r a ha).FullSubcategory),
    IsIso ((pbcIntegralDatum P.coefficients.l P.extension).ordinaryToCompleted g
      ((cbcSupport (pbcIntegralDatum P.coefficients.l P.extension) c).obj K.obj)) ∧
    IsIso ((pbcIntegralDatum P.coefficients.l P.extension).ordinaryToCompleted gb
      ((cbcJ (pbcIntegralDatum P.coefficients.l P.extension) c.i).obj K.obj)) ∧
    IsIso ((pbcIntegralDatum P.coefficients.l P.extension).ordinaryToCompleted g' K.obj) ∧
    (cbcDatumOrdinaryExchange (pbcIntegralDatum P.coefficients.l P.extension) sj).app K.obj =
      (cbcBeta (pbcIntegralDatum P.coefficients.l P.extension) g' c'.i c.i gb sj.w
        (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst
          sj.hom_snd)).hom.app K.obj := by sorry

end AlgebraicGeometry.Scheme
