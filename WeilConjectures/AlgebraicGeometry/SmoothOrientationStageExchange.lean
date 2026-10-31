/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothOrientationCoefficientFamily
public import WeilConjectures.AlgebraicGeometry.SmoothOrientationTransportSquare
public import WeilConjectures.AlgebraicGeometry.AdmissibleVerdierExchange
public import WeilConjectures.AlgebraicGeometry.IntegralOrientedExchangeSquares
public import WeilConjectures.AlgebraicGeometry.FieldOrientedExchangeSquares
import all WeilConjectures.AlgebraicGeometry.AdicPurityScalarNaturalityData

/-! # Site exchange comparisons under the smooth orientation

Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
thm-pod-global-verdier-duality.proof.md, second paragraph
(blueprint: def-pod-smooth-orientation-stage-exchange).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local instance 2000] IntermediateField.algebra'
attribute [local instance 2000] ConstructibleExceptionalCoefficients.category
attribute [local irreducible] CategoryTheory.Functor.mapIso CategoryTheory.Iso.trans
attribute [local irreducible]
  RationalSmoothPurityCanonical.integralIso
  RationalSmoothPurityCanonical.rationalIso
  RationalSmoothPurityCanonical.smallModelIso
  RationalSmoothPurityCanonical.commonIso
  RationalSmoothPurityCanonical.commonSourceComparison
  RationalSmoothPurityCanonical.sourceScalar

/-- The coefficient exchange at `Y = Spec k`, on any two coefficient stages.
The exchange arrows are the isomorphism components of the recorded admissible
exchange, and the orientation clause is the explicit Hom/evaluation transport.
Source: latest blueprint, global Verdier duality proof, coefficient comparisons
(blueprint: def-pod-smooth-orientation-stage-exchange). -/
@[irreducible] def canonicalExchangeAtStage
    (P : PurityFiniteSetting.{u})
    {X : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (f : X ⟶ Spec (.of P.field.k))
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (s : SmoothOrientationCoefficient P)
    (K : ConstructibleExceptionalCoefficients.C.{u, u} P.coefficients.l
      P.coefficients.Qbar X (s.stage P)) :
      Prop :=
  letI : ∀ x : X, Invertible (P.coefficients.l : X.residueField x) :=
    fun x ↦ (purAdicResidueUnit P.field P.coefficients X x).invertible
  letI : ∀ x : Spec (.of P.field.k),
      Invertible (P.coefficients.l : (Spec (.of P.field.k)).residueField x) :=
    fun x ↦ (purAdicResidueUnit P.field P.coefficients (Spec (.of P.field.k)) x).invertible
  letI : (Spec (.of P.field.k)).Over (Spec (.of P.field.k)) := ⟨𝟙 _⟩
  letI : (Spec (.of P.field.k) ↘ Spec (.of P.field.k)).IsOver (Spec (.of P.field.k)) :=
    ⟨Category.comp_id _⟩
  letI : LocallyOfFiniteType (Spec (.of P.field.k) ↘ Spec (.of P.field.k)) := by infer_instance
  letI : QuasiCompact (Spec (.of P.field.k) ↘ Spec (.of P.field.k)) := by infer_instance
  letI : IsSeparated (Spec (.of P.field.k) ↘ Spec (.of P.field.k)) := by infer_instance
  ∀ (hf : f.IsOver (Spec (.of P.field.k))) (hsep : IsSeparated f)
    (hlft : LocallyOfFiniteType f) (hqc : QuasiCompact f),
    let _ := hf
    let _ := hsep
    let _ := hlft
    let _ := hqc
    ∀ (Sf : ConstructibleExceptionalCoefficients.System.{u, u} P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different (f := f))
    (SY : ConstructibleExceptionalCoefficients.System.{u, u} P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different
      (f := (Spec (.of P.field.k) ↘ Spec (.of P.field.k))))
    (SX : ConstructibleExceptionalCoefficients.System.{u, u} P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different
      (f := f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))))
    ,
    let cf := integralExceptionalCompactification P.field f
    let cY := integralExceptionalCompactification P.field
      (Spec (.of P.field.k) ↘ Spec (.of P.field.k))
    let cX := integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))
    letI : SmoothOfRelativeDimension d
        (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) := by
      change SmoothOfRelativeDimension d (f ≫ 𝟙 _)
      simpa only [Category.comp_id] using
        (inferInstance : SmoothOfRelativeDimension d f)
    ∃ p : AdmissibleVerdierExchange.Package P.coefficients.l P.coefficients.Qbar P.field
      P.coefficients.different f
      (Spec (.of P.field.k) ↘ Spec (.of P.field.k)) Sf SY SX cf cY cX
      (AdmissibleVerdierExchange.admissible P.coefficients.l P.coefficients.Qbar P.field
        P.coefficients.different f cf cY cX),
      smoothIntegralExtensionExchangeSquares P f d Sf SY SX p ∧
      smoothIntegralReductionExchangeSquares P f d Sf SY SX p ∧
      smoothCommonStageExchangeSquares P f d Sf SY SX p ∧
      match s, K with
      | .finite E n, K =>
        let E₀ := AdicPurityScalarNaturality.fieldStage P.field P.coefficients E
        ∀ (m : ℕ+) (hmn : (m : ℕ) ≤ n)
          (hs : AdmissibleVerdierExchange.admissible P.coefficients.l P.coefficients.Qbar
            P.field P.coefficients.different f cf cY cX (.finite E₀ n))
          (ht : AdmissibleVerdierExchange.admissible P.coefficients.l P.coefficients.Qbar
            P.field P.coefficients.different f cf cY cX (.finite E₀ m)),
        let a := PurCompactSupport.finiteQuotientChange P.coefficients.l E.val
          n m n.pos m.pos hmn
        ∃ (QX : ConstructibleExceptionalCoefficients.Scalar.{u, u} P.coefficients.l
            P.coefficients.Qbar (s := .finite E₀ n) (t := .finite E₀ m) a X)
          (QY : ConstructibleExceptionalCoefficients.Scalar.{u, u} P.coefficients.l
            P.coefficients.Qbar (s := .finite E₀ n) (t := .finite E₀ m)
            a (Spec (.of P.field.k)))
          (QZ : ConstructibleExceptionalCoefficients.Scalar.{u, u} P.coefficients.l
            P.coefficients.Qbar (s := .finite E₀ n) (t := .finite E₀ m)
            a (Spec (.of P.field.k)))
          (b : VerdierExchange.StageScalar P.coefficients.l P.coefficients.Qbar
            (p.stage (.finite E₀ n)) (p.stage (.finite E₀ m))
            QX.functor QY.functor QZ.functor),
        (∀ M, (finiteTorConstructible P.coefficients.l E.val m m.pos
            (Spec (.of P.field.k))).ι.map
            ((b.exceptional.q P.coefficients.l P.coefficients.Qbar).hom.app M) ≫
            (Sf.ring.left cf (.finite E₀ m)).hom.app (QX.functor.obj M) ≫
            (PurCompactSupport.image ((ConstructibleExceptionalCoefficients.RingStage.finite
              E₀ m).coefficients P.coefficients.l) cf).map (QX.realization.hom.app M) =
          QY.realization.hom.app ((Sf.ring.operation cf (.finite E₀ n)).F.obj M) ≫
            (pbcDerivedExtend (a.map (Spec (.of P.field.k)))).map
              ((Sf.ring.left cf (.finite E₀ n)).hom.app M) ≫
            (PurCompactSupport.comparison a cf).app M.obj) ∧
        (∀ M, (finiteTorConstructible P.coefficients.l E.val m m.pos
            (Spec (.of P.field.k))).ι.map
            ((b.structureX.q P.coefficients.l P.coefficients.Qbar).hom.app M) ≫
            (SX.ring.left cX (.finite E₀ m)).hom.app (QX.functor.obj M) ≫
            (PurCompactSupport.image ((ConstructibleExceptionalCoefficients.RingStage.finite
              E₀ m).coefficients P.coefficients.l) cX).map (QX.realization.hom.app M) =
          QZ.realization.hom.app ((SX.ring.operation cX (.finite E₀ n)).F.obj M) ≫
            (pbcDerivedExtend (a.map (Spec (.of P.field.k)))).map
              ((SX.ring.left cX (.finite E₀ n)).hom.app M) ≫
            (PurCompactSupport.comparison a cX).app M.obj) ∧
        (finiteTorConstructible P.coefficients.l E.val m m.pos
            (Spec (.of P.field.k))).ι.map b.unit.hom ≫
            (p.ring (.finite E₀ m)).unitIso.hom =
          QZ.realization.hom.app (p.unit (.finite E₀ n)) ≫
            (pbcDerivedExtend (a.map (Spec (.of P.field.k)))).map
              (p.ring (.finite E₀ n)).unitIso.hom ≫
            VerdierExchange.ringUnitScalar P.coefficients.l
              (s := .finite E₀ n) (t := .finite E₀ m) a (Spec (.of P.field.k)) ∧
        let γs := smoothOrientationAtStage P
          (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) d SX cX
          (.finite E n) (p.unit (.finite E₀ n))
        let γt := smoothOrientationAtStage P
          (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) d SX cX
          (.finite E m) (p.unit (.finite E₀ m))
        let hQ := smoothFiniteOrientationSourceComparison P
          (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) d SX cX E n m hmn
          QX QZ (p.unit (.finite E₀ n)) (p.unit (.finite E₀ m)) b.unit
        QX.functor.map γs.2.hom ≫ (b.kappaX P.coefficients.l P.coefficients.Qbar).hom =
            hQ.hom ≫ γt.2.hom ∧
        QX.functor.map γs.2.inv ≫ hQ.hom =
            (b.kappaX P.coefficients.l P.coefficients.Qbar).hom ≫ γt.2.inv ∧
        smoothOrientationExchangeSquare P.coefficients.l P.coefficients.Qbar
          (p.stage (.finite E₀ n)) (p.stage (.finite E₀ m)) b
          (p.conclusion (.finite E₀ n) hs) (p.conclusion (.finite E₀ m) ht) K ∧
        smoothOrientationTransportSquare P.coefficients.l P.coefficients.Qbar
          (p.stage (.finite E₀ n)) (p.stage (.finite E₀ m)) b γs.1 γt.1 γs.2 γt.2 hQ.hom K
      | .integral E, K =>
        smoothRationalizationExchangeSquares P f d Sf SY SX p E K
      | .rational E, K =>
        smoothRationalScalarExchangeSquares P f d Sf SY SX p E K
      | .closed, _ => True

end WeilConjectures
