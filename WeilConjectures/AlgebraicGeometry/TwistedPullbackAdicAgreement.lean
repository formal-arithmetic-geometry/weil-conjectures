/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.TwistedPullbackScalarShifts

/-! # Agreement of the rational twisted scalar comparison with the adic one

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, purity transport,
identification of a with adic scalar naturality
(blueprint: def-pur-twisted-pullback-adic-agreement).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TwistedPullbackScalars
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L)

/-- Integral q, using exactly the integral scalar shift, completed tensor comparison,
and roots-induced scalar map of the degree-zero Tate line.
Source: purity transport, integral representative of q
(blueprint: def-pur-twisted-pullback-adic-agreement). -/
def integralQ (W : Scheme.{u}) [∀ x : W, Invertible (l : W.residueField x)]
    (d : ℕ) (K : sfIntegralConstructibleCategory l E W) :=
  (RationalSmoothPurityCanonical.integralScalarShift l E L i W (2 * (d : ℤ))).app
      ((integralTwist l E W d).obj K) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      (integralTensorScalarComparison l E L i W K
          (sfIntegralTwistingCoefficient l E W (d : ℤ)) ≪≫
        (constructibleIntegralTensor l L W).mapIso
          (Iso.prod (Iso.refl _) (CanonicalTate.integralScalarLine l E L i W d)))

/-- Integral twisted pullback, with the same tensor order as H.
Source: purity transport, common integral objects
(blueprint: def-pur-twisted-pullback-adic-agreement). -/
def integralH {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :=
  constructibleIntegralPullback l E f ⋙ integralD l E X d

/-- Integral a is q followed by D applied to the specified scalar/pullback map.
Source: purity transport, rationalization of the displayed comparison
(blueprint: def-pur-twisted-pullback-adic-agreement). -/
def integralA {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ)
    (K : sfIntegralConstructibleCategory l E Y) :=
  integralQ l E L i X d ((constructibleIntegralPullback l E f).obj K) ≪≫
    (integralD l L X d).mapIso (integralPullbackScalarComparison l E L i f K)

section Adic
variable (B : FiniteFieldDatum.{u}) (C : B.CoefficientDatum)
variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of B.k))] [Y.Over (Spec (.of B.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of B.k))] [QuasiCompact (X ↘ Spec (.of B.k))]
  [IsSeparated (X ↘ Spec (.of B.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of B.k))] [QuasiCompact (Y ↘ Spec (.of B.k))]
  [IsSeparated (Y ↘ Spec (.of B.k))]
  [∀ x : X, Invertible (C.l : X.residueField x)]
  [∀ y : Y, Invertible (C.l : Y.residueField y)]
  (f : X ⟶ Y) [f.IsOver (Spec (.of B.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

/-- Agreement with the recorded adic a, after the actual completion maps and the
normalized tensor/termwise-twist identifications. The first clause identifies the
rational map with this integral map; the second identifies that same map with
sourceScalarComponent. Neither a new adic map nor an arbitrary lattice is chosen.
Source: purity transport, final agreement with adic scalar naturality
(blueprint: def-pur-twisted-pullback-adic-agreement). -/
def AdicAgreement (hC : AdicPurityScalarNaturality.ScalarClosed B C X Y)
    (s : ∀ R : Fields C.l C.Qbar, ShiftData C.l R.val X d) : Prop :=
  ∀ (R S : Fields C.l C.Qbar) (h : R ≤ S)
    (K : AdicPurityScalarNaturality.Cat B C R Y),
    let Kc : sfIntegralConstructibleCategory C.l R.val Y := ⟨K.obj, K.property.1⟩
    let P := (constructibleIntegralPullback C.l R.val f).obj Kc
    let SK := (sfConstructibleIntegralScalarExtension 0 C.l
      (Fact.out : C.l.Prime).ne_zero R.val S.val (IntermediateField.inclusion h) Y).obj Kc
    let PS := (constructibleIntegralPullback C.l S.val f).obj SK
    let chiY := scalarCompletionIso C.l R.val S.val (IntermediateField.inclusion h) Y
      K.obj K.property.1.1
    let A := integralA C.l R.val S.val (IntermediateField.inclusion h) f d Kc
    HEq (a C.l R.val S.val (IntermediateField.inclusion h) f d
      ((sfRationalConstructibleLocalization C.l R.val Y).obj Kc)).hom
      ((sfRationalConstructibleLocalization C.l S.val X).map A.hom) ∧
    HEq ((integralOrdinaryDerivedScalar C.l R.val S.val (IntermediateField.inclusion h) X).map
        (shiftedBetaFrom C.l R.val X d (s R).beta P).inv ≫
      (scalarCompletionIso C.l R.val S.val (IntermediateField.inclusion h) X
        ((integralH C.l R.val f d).obj Kc).obj
        ((integralH C.l R.val f d).obj Kc).property.1).hom ≫
      A.hom.hom ≫ (shiftedBetaFrom C.l S.val X d (s S).beta PS).hom ≫
      (shiftFunctor _ (2 * (d : ℤ))).map
        ((sfIntegralTwistingFunctor C.l S.val X (d : ℤ)).map
          ((integralDerivedPullback C.l S.val f).map chiY.inv)))
      (AdicPurityScalarNaturality.sourceScalarComponent B C f d hC R S h K).hom

end Adic
end WeilConjectures.TwistedPullbackScalars
