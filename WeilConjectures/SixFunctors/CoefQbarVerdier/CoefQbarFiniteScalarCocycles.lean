/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coef.CoefQbarRationalScalarCocycles

/-! # Exceptional scalar cocycles on finite stages

Source: blueprint thm-coef-qbar-verdier, proof steps 6--9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] WeilConjectures.CoefQbarTensor
  WeilConjectures.CoefQbarPullback
  WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageCategory
  WeilConjectures.sfRationalScalarExtension WeilConjectures.sfRationalScalarComp
  WeilConjectures.sfRationalScalarUnit WeilConjectures.sfRationalConstructibleLocalization
  CategoryTheory.ScalarLocalization.category CategoryTheory.ScalarLocalization.composition

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

private theorem cocycle_congr
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
    {U₀ : C₀ ⥤ C₁} {U₁ : C₁ ⥤ C₂} {U₂ : C₀ ⥤ C₂}
    {V₀ : D₀ ⥤ D₁} {V₁ : D₁ ⥤ D₂} {V₂ : D₀ ⥤ D₂}
    (b₀ : F₀ ⋙ V₀ ≅ U₀ ⋙ F₁) (b₁ : F₁ ⋙ V₁ ≅ U₁ ⋙ F₂)
    (b₂ : F₀ ⋙ V₂ ≅ U₂ ⋙ F₂)
    (aU aU' : U₀ ⋙ U₁ ≅ U₂) (aV aV' : V₀ ⋙ V₁ ≅ V₂)
    (hU : aU = aU') (hV : aV = aV')
    (hc : CoefficientCocycleCondition F₀ F₁ F₂ b₀ b₁ b₂ aU' aV') :
    CoefficientCocycleCondition F₀ F₁ F₂ b₀ b₁ b₂ aU aV := by
  subst aU' aV'
  exact hc

private theorem cocycle_pair_congr
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
    (G₀ : D₀ ⥤ C₀) (G₁ : D₁ ⥤ C₁) (G₂ : D₂ ⥤ C₂)
    {U₀ : C₀ ⥤ C₁} {U₁ : C₁ ⥤ C₂} {U₂ : C₀ ⥤ C₂}
    {V₀ : D₀ ⥤ D₁} {V₁ : D₁ ⥤ D₂} {V₂ : D₀ ⥤ D₂}
    (b₀ : F₀ ⋙ V₀ ≅ U₀ ⋙ F₁) (b₁ : F₁ ⋙ V₁ ≅ U₁ ⋙ F₂)
    (b₂ : F₀ ⋙ V₂ ≅ U₂ ⋙ F₂)
    (d₀ : G₀ ⋙ U₀ ≅ V₀ ⋙ G₁) (d₁ : G₁ ⋙ U₁ ≅ V₁ ⋙ G₂)
    (d₂ : G₀ ⋙ U₂ ≅ V₂ ⋙ G₂)
    (aU aU' : U₀ ⋙ U₁ ≅ U₂) (aV aV' : V₀ ⋙ V₁ ≅ V₂)
    (hU : aU = aU') (hV : aV = aV')
    (hc : CoefficientCocycleCondition F₀ F₁ F₂ b₀ b₁ b₂ aU' aV')
    (hd : CoefficientCocycleCondition G₀ G₁ G₂ d₀ d₁ d₂ aV' aU') :
    CoefficientCocycleCondition F₀ F₁ F₂ b₀ b₁ b₂ aU aV ∧
      CoefficientCocycleCondition G₀ G₁ G₂ d₀ d₁ d₂ aV aU := by
  exact ⟨cocycle_congr F₀ F₁ F₂ b₀ b₁ b₂ aU aU' aV aV' hU hV hc,
    cocycle_congr G₀ G₁ G₂ d₀ d₁ d₂ aV aV' aU aU' hV hU hd⟩

namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition associator unitor)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

omit [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))] in
/-- Both exceptional scalar cocycles on the prescribed literal finite stages.
Source: thm-coef-qbar-verdier, retained steps 6--8
(blueprint: lem-coef-qbar-finite-scalar-cocycles).

Proof: specialize rational_scalar_cocycles to the small coefficient-field models.
Their composite algebra map is the prescribed inclusion by coefficientInclusion_laws.
The uniqueness characterization of each chosen stage associator identifies it with
the literal scalar associator. Transport the two cocycle equations along these
identifications, retaining the actual left and right scalar comparisons. -/
theorem finite_scalar_cocycles (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))
    {E L M : Index l Ω} (h : E ≤ L) (k : L ≤ M) :
    CoefficientCocycleCondition
    (finiteLeft D l hl Ω X f c S E) (finiteLeft D l hl Ω X f c S L)
    (finiteLeft D l hl Ω X f c S M)
    (finiteLeftScalar D l hl Ω X f c S E L h)
    (finiteLeftScalar D l hl Ω X f c S L M k)
    (finiteLeftScalar D l hl Ω X f c S E M (h.trans k))
    (associator l Ω X E L M h k) (associator l Ω Y E L M h k) ∧
    CoefficientCocycleCondition
    (finiteRight D l hl Ω X f c S E) (finiteRight D l hl Ω X f c S L)
    (finiteRight D l hl Ω X f c S M)
    (finiteRightScalar D l hl Ω X f c S E L h)
    (finiteRightScalar D l hl Ω X f c S L M k)
    (finiteRightScalar D l hl Ω X f c S E M (h.trans k))
    (associator l Ω Y E L M h k) (associator l Ω X E L M h k) := by
  have H := rational_scalar_cocycles D l hl X f c S
    (fieldStage l Ω E) (fieldStage l Ω L)
    (fieldStage l Ω M) (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω L M k)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E M (h.trans k))
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k)
  dsimp only at H
  rcases H with ⟨Hleft, Hright⟩
  have hx := (GeneralAlgebraicallyClosedCoefficients.associator_existsUnique
    l Ω X E L M h k).exists.choose_spec
  have hy := (GeneralAlgebraicallyClosedCoefficients.associator_existsUnique
    l Ω Y E L M h k).exists.choose_spec
  change HEq _ _ at hx
  change HEq _ _ at hy
  delta GeneralAlgebraicallyClosedCoefficients.stageCategory at hx hy
  have hx' := eq_of_heq hx
  have hy' := eq_of_heq hy
  let aX := GeneralAlgebraicallyClosedCoefficients.scalarAssociator l
    (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L) (Coefficient.{u} l Ω M)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω L M k)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E M (h.trans k))
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k) X
  let aY := GeneralAlgebraicallyClosedCoefficients.scalarAssociator l
    (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L) (Coefficient.{u} l Ω M)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω L M k)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E M (h.trans k))
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k) Y
  have hc := cocycle_pair_congr
    (S.ring.operation c (.rational (fieldStage l Ω E))).F
    (S.ring.operation c (.rational (fieldStage l Ω L))).F
    (S.ring.operation c (.rational (fieldStage l Ω M))).F
    (S.ring.operation c (.rational (fieldStage l Ω E))).G
    (S.ring.operation c (.rational (fieldStage l Ω L))).G
    (S.ring.operation c (.rational (fieldStage l Ω M))).G
    ((S.fields.rationalComparison c (fieldStage l Ω E) (fieldStage l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h)).q)
    ((S.fields.rationalComparison c (fieldStage l Ω L) (fieldStage l Ω M)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω L M k)).q)
    ((S.fields.rationalComparison c (fieldStage l Ω E) (fieldStage l Ω M)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E M (h.trans k))).q)
    ((S.fields.rationalComparison c (fieldStage l Ω E) (fieldStage l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h)).b)
    ((S.fields.rationalComparison c (fieldStage l Ω L) (fieldStage l Ω M)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω L M k)).b)
    ((S.fields.rationalComparison c (fieldStage l Ω E) (fieldStage l Ω M)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E M (h.trans k))).b)
    (by with_unfolding_all exact associator l Ω X E L M h k) aX
    (by with_unfolding_all exact associator l Ω Y E L M h k) aY
    (by with_unfolding_all exact hx') (by with_unfolding_all exact hy') Hleft Hright
  with_unfolding_all exact hc

end WeilConjectures.CoefQbarVerdier
