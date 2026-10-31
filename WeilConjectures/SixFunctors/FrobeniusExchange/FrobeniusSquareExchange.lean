/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationCoherence
public import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusWitnessedCompactification
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenComparison
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
public import WeilConjectures.Compactification.CategoryBaseChange
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SmoothPurity.Sf.SfIntegralDirectImageConstructible
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.DeligneLaumon.WeilCompactSupportCohomology
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

import all WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
import WeilConjectures.SmoothPurity.Integral.IntegralDerivedPullbackLinear
import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientExchangeInvertible
import WeilConjectures.SixFunctors.Supporting.DirectImageCoefficientExchangeInvertible

/-! # Coefficient passage for the specified operation exchanges

Source: slopmaster2 blueprint, `def:weil-direct-image-object` and
`def:weil-compact-support-object`; Deligne, Weil II, (1.1.10)--(1.1.14)
(blueprint: def-weil-operation-exchange-coefficient-descent).

## Main definitions

- `SupportModel`, `modelExchange`: retain the direct or chosen compactification recipe.
- `modelRationalExchange`: literal localization of the integral exchange.
- `stageBeta`, `commonStageExchange`: canonical scalar maps and common-stage descent.
- `intrinsicCompactificationComparison`: normalized transport of the landed comparison.
- `intrinsicCompactificationComparison_refinement`: its recorded-refinement normalization.
- `transportCompact`: the specified witnessed compactification transport.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option Elab.async true
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.ScalarLocalization.composition
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor

namespace WeilConjectures.FrobeniusExchange

section GenericLocalization
universe uR uC uD vC vD
variable (R : Type uR) [CommRing R] (p : R)
  {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
  (F : C ⥤ D) [F.Additive] [F.Linear R]

/-- Extend the actual integral Hom map by the tensor universal property.
Private linear-category argument. -/
private def genericLocalizedHom (K L : ScalarLocalization R C p) :
    (K ⟶ L) →ₗ[Localization.Away p]
      ((⟨F.obj K.obj⟩ : ScalarLocalization R D p) ⟶ ⟨F.obj L.obj⟩) :=
  (F.mapLinearMap R).baseChange
    (Localization.Away p)

private theorem genericLocalizedHom_tmul (K L : ScalarLocalization R C p)
    (c : Localization.Away p) (a : K.obj ⟶ L.obj) :
    genericLocalizedHom R p F K L (c ⊗ₜ[R] a) = c ⊗ₜ[R] F.map a :=
  LinearMap.baseChange_tmul _ _ _

attribute [local irreducible] genericLocalizedHom

/-- The explicit tensor action satisfies the functor laws.
Source: blueprint rational paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: on pure tensors use the integral functor laws and the tensor-composition
formula of def-weil-rationalization-karoubi. Extend by additivity in both variables.
The identity is one tensored with the integral identity. -/
private theorem genericLocalizedHom_laws :
    (∀ K : ScalarLocalization R C p,
      genericLocalizedHom R p F K K (𝟙 K) =
        𝟙 (⟨F.obj K.obj⟩ : ScalarLocalization R D p)) ∧
    (∀ (K L M : ScalarLocalization R C p) (a : K ⟶ L) (b : L ⟶ M),
      genericLocalizedHom R p F K M (a ≫ b) =
        genericLocalizedHom R p F K L a ≫ genericLocalizedHom R p F L M b) := by
  constructor
  · intro K
    change genericLocalizedHom R p F K K
      ((1 : Localization.Away p) ⊗ₜ[R] (𝟙 K.obj)) =
        (1 : Localization.Away p) ⊗ₜ[R] (𝟙 (F.obj K.obj))
    rw [genericLocalizedHom_tmul, F.map_id]
  · intro K L M a b
    change genericLocalizedHom R p F K M
      (ScalarLocalization.composition _ _ _ K.obj L.obj M.obj b a) =
        ScalarLocalization.composition _ _ _ _ _ _
          (genericLocalizedHom R p F L M b) (genericLocalizedHom R p F K L a)
    induction b using TensorProduct.induction_on with
    | zero => simp only [LinearMap.map_zero, LinearMap.zero_apply]
    | tmul d b =>
      induction a using TensorProduct.induction_on with
      | zero => simp only [LinearMap.map_zero]
      | tmul c a =>
        rw [ScalarLocalization.composition_tmul]
        rw [genericLocalizedHom_tmul, genericLocalizedHom_tmul,
          genericLocalizedHom_tmul, ScalarLocalization.composition_tmul, F.map_comp]
      | add a a' ha ha' => simp only [LinearMap.map_add, ha, ha']
    | add b b' hb hb' => simp only [LinearMap.map_add, LinearMap.add_apply, hb, hb']

private theorem genericLocalizedHom_naturality
    (G : C ⥤ D) [G.Additive] [G.Linear R] (τ : F ⟶ G)
    (K L : ScalarLocalization R C p) (a : K ⟶ L) :
    genericLocalizedHom R p F K L a ≫
        (1 ⊗ₜ[R] τ.app L.obj :
          (⟨F.obj L.obj⟩ : ScalarLocalization R D p) ⟶ ⟨G.obj L.obj⟩) =
      (1 ⊗ₜ[R] τ.app K.obj :
          (⟨F.obj K.obj⟩ : ScalarLocalization R D p) ⟶ ⟨G.obj K.obj⟩) ≫
        genericLocalizedHom R p G K L a := by
  change ScalarLocalization.composition _ _ _ _ _ _
      ((1 : Localization.Away p) ⊗ₜ τ.app L.obj)
      (genericLocalizedHom R p F K L a) =
    ScalarLocalization.composition _ _ _ _ _ _ (genericLocalizedHom R p G K L a)
      ((1 : Localization.Away p) ⊗ₜ τ.app K.obj)
  induction a using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearMap.zero_apply]
  | tmul c a =>
    rw [genericLocalizedHom_tmul, genericLocalizedHom_tmul]
    simp only [ScalarLocalization.composition_tmul, one_mul, mul_one, τ.naturality a]
  | add a b ha hb => simp only [LinearMap.map_add, LinearMap.add_apply, ha, hb]

end GenericLocalization

section RawLocalization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{u}}
  (F : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y)
  [F.Additive] [F.Linear (Padic.coefficientExtensionIntegers l E)]

/-- Extend the actual integral Hom map by the tensor universal property.
Source: blueprint rational-coefficient paragraphs
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def localizedHom (K L : sfRationalConstructibleCategory l E X) :
    (K ⟶ L) →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer l E)]
      ((⟨F.obj K.obj⟩ : sfRationalConstructibleCategory l E Y) ⟶ ⟨F.obj L.obj⟩) :=
  (F.mapLinearMap (Padic.coefficientExtensionIntegers l E)).baseChange
    (Localization.Away (Padic.coefficientExtensionUniformizer l E))

/-- The explicit tensor action satisfies the functor laws.
Source: blueprint rational paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: on pure tensors use the integral functor laws and the tensor-composition
formula of def-weil-rationalization-karoubi. Extend by additivity in both variables.
The identity is one tensored with the integral identity. -/
theorem localizedHom_laws :
    (∀ K : sfRationalConstructibleCategory l E X,
      localizedHom l E F K K (𝟙 K) =
        𝟙 (⟨F.obj K.obj⟩ : sfRationalConstructibleCategory l E Y)) ∧
    (∀ (K L M : sfRationalConstructibleCategory l E X) (a : K ⟶ L) (b : L ⟶ M),
      localizedHom l E F K M (a ≫ b) =
        localizedHom l E F K L a ≫ localizedHom l E F L M b) := by
  exact genericLocalizedHom_laws (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E) F

/-- Raw scalar localization of an actual operation, with unchanged objects and
explicit tensor Hom maps. No idempotent completion or rational reduction occurs.
Source: blueprint rational-coefficient paragraphs
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def localizedFunctor :
    sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E Y where
  obj K := ⟨F.obj K.obj⟩
  map {K L} a := localizedHom l E F K L a
  map_id K := (localizedHom_laws l E F).1 K
  map_comp a b := (localizedHom_laws l E F).2 _ _ _ a b

variable (G : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y)
  [G.Additive] [G.Linear (Padic.coefficientExtensionIntegers l E)] (τ : F ⟶ G)

/-- Naturality of the explicitly localized components holds for every tensor Hom.
Source: blueprint rational paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: for one pure tensor the equation is integral naturality multiplied by its
scalar. Tensor balancing and addition prove the equation for an arbitrary Hom. -/
theorem localizedTransformation_naturality (K L : sfRationalConstructibleCategory l E X)
    (a : K ⟶ L) :
    (localizedFunctor l E F).map a ≫
        (sfRationalConstructibleLocalization l E Y).map (τ.app L.obj) =
      (sfRationalConstructibleLocalization l E Y).map (τ.app K.obj) ≫
        (localizedFunctor l E G).map a := by
  exact genericLocalizedHom_naturality (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E) F G τ K L a

/-- Localize precisely the integral exchange components, tensoring them with one.
Source: blueprint rational-coefficient paragraphs
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def localizedTransformation : localizedFunctor l E F ⟶ localizedFunctor l E G where
  app K := (sfRationalConstructibleLocalization l E Y).map (τ.app K.obj)
  naturality K L a := localizedTransformation_naturality l E F G τ K L a

private theorem localizedHom_tmul (K L : sfRationalConstructibleCategory l E X)
    (c : Localization.Away (Padic.coefficientExtensionUniformizer l E))
    (a : K.obj ⟶ L.obj) :
    localizedHom l E F K L (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] a) =
      c ⊗ₜ[Padic.coefficientExtensionIntegers l E] F.map a :=
  LinearMap.baseChange_tmul _ _ _

private theorem localizedFunctor_comp {Z : Scheme.{u}}
    (H : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E Z)
    [H.Additive] [H.Linear (Padic.coefficientExtensionIntegers l E)] :
    localizedFunctor l E (F ⋙ H) = localizedFunctor l E F ⋙ localizedFunctor l E H := by
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro K L a
  apply heq_of_eq
  change localizedHom l E (F ⋙ H) K L a =
    localizedHom l E H _ _ (localizedHom l E F K L a)
  induction a using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero]
  | tmul c a =>
    rw [localizedHom_tmul, localizedHom_tmul, localizedHom_tmul]
    rfl
  | add a b ha hb => simp only [LinearMap.map_add, ha, hb]

attribute [local irreducible] localizedHom localizedFunctor

end RawLocalization

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

section CoefficientPassage
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}}
  [xo : X.Over (Spec (.of K₀))] [yo : Y.Over (Spec (.of K₀))]
  [xft : LocallyOfFiniteType (X ↘ Spec (.of K₀))] [xqc : QuasiCompact (X ↘ Spec (.of K₀))]
  [yft : LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [yqc : QuasiCompact (Y ↘ Spec (.of K₀))]
  (f : X ⟶ Y) [fo : f.IsOver (Spec (.of K₀))]
  [ix : ∀ x : X, Invertible (l : X.residueField x)]
  [iy : ∀ y : Y, Invertible (l : Y.residueField y)]
  (gX : X ⟶ X) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]

attribute [local irreducible] integralDerivedPullback

/-- Integral pullback is additive and linear for constant completed scalars.
Source: blueprint scalar-localization paragraph; Stacks 099N(5)
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: use its single K-flat quotient presentation. Termwise inverse image and
its scalar tensor maps are additive and O_E-linear; the quotient transitions,
restriction and normalized total-limit maps respect these identities. -/
theorem pullback_linear (T : Scheme.{u})
    [∀ t : T, Invertible (l : T.residueField t)] (g : T ⟶ T) :
    (constructibleIntegralPullback l E g).Additive ∧
      (constructibleIntegralPullback l E g).Linear (Padic.coefficientExtensionIntegers l E) := by
  have h := integralDerivedPullback_linear l E g
  constructor
  · exact ⟨fun {K N a b} ↦ by
      apply ObjectProperty.hom_ext
      exact h.1.map_add⟩
  · exact ⟨fun {K N} a c ↦ by
      apply ObjectProperty.hom_ext
      exact h.2.map_smul a.hom c⟩

/-- The localized pullback is the recorded rational pullback, on objects and
all tensor Hom maps, without adding an idempotent completion.
Source: def-weil-derived-pullback-tensor-hom, rational normalization
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: both functors keep the integral representative and send each pure tensor
a tensor v to a tensor g*(v). Tensor induction gives equality on all Homs;
functor extensionality and proof irrelevance identify the functors. -/
theorem localizedPullback_eq (T : Scheme.{u})
    [∀ t : T, Invertible (l : T.residueField t)] (g : T ⟶ T) :
    letI := (pullback_linear l E T g).1
    letI := (pullback_linear l E T g).2
    localizedFunctor l E (constructibleIntegralPullback l E g) =
      rationalDerivedPullback l E g := by
  let := (pullback_linear l E T g).1
  let := (pullback_linear l E T g).2
  apply (rationalDerivedPullback_existsUnique l E g).unique
  · refine ⟨?_, fun K ↦ rfl, ?_⟩
    · exact ⟨fun {K L} {a b} ↦ (localizedHom l E _ K L).map_add a b⟩
    · intro K L a c
      apply heq_of_eq
      exact LinearMap.baseChange_tmul _ _ _
  · exact (rationalDerivedPullback_existsUnique l E g).exists.choose_spec

end CoefficientPassage

/-- Select one of the two specified recipes, retaining the compactification
and its actual Frobenius squares in the compact-support case.
Source: blueprint `def:weil-direct-image-object`, `def:weil-compact-support-object`
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
inductive SupportModel {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
  | direct (w : gX ≫ f = f ≫ gY)
  | compact (c : Compactification f) (gB : c.Z ⟶ c.Z)
      (wp : gB ≫ c.g = c.g ≫ gY) (sj : IsPullback gX c.i c.i gB)

section CoefficientDescent
variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}}
  [xo : X.Over (Spec (.of K₀))] [yo : Y.Over (Spec (.of K₀))]
  [xft : LocallyOfFiniteType (X ↘ Spec (.of K₀))] [xqc : QuasiCompact (X ↘ Spec (.of K₀))]
  [yft : LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [yqc : QuasiCompact (Y ↘ Spec (.of K₀))]
  (f : X ⟶ Y) [fo : f.IsOver (Spec (.of K₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [ix : ∀ x : X, Invertible (l : X.residueField x)]
  [iy : ∀ y : Y, Invertible (l : Y.residueField y)]
  (gX : X ⟶ X) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY] (M : SupportModel f gX gY)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The already constructed actual integral operation selected by the retained recipe.
Source: blueprint coefficient passages
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelFunctor :
    sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y :=
  match M with
  | .direct _ => directImageFunctor l E K₀ hl f
  | .compact c _ _ _ => sfCompactSupportFiniteIntegralFunctor l K₀ hl c E

/-- The specified integral exchange, selected without selecting any morphism data.
Source: blueprint coefficient passages
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelExchange : modelFunctor l K₀ hl f gX gY M E ⋙
      constructibleIntegralPullback l E gY ⟶
    constructibleIntegralPullback l E gX ⋙ modelFunctor l K₀ hl f gX gY M E :=
  match M with
  | .direct w => directIntegral l E K₀ hl f gX gY w
  | .compact c gB wp sj => compactIntegral l E K₀ hl f c gX gB gY wp sj

attribute [local irreducible] modelExchange

set_option linter.unusedSectionVars false in
/-- The inherited linearity proofs for the selected actual operation.
Source: blueprint scalar localization
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
theorem modelLinear : (modelFunctor l K₀ hl f gX gY M E).Additive ∧
    (modelFunctor l K₀ hl f gX gY M E).Linear (Padic.coefficientExtensionIntegers l E) := by
  cases M with
  | direct w => exact directImage_linear l E K₀ hl f
  | compact c gB wp sj => exact sfCompactSupportFiniteIntegralFunctor_linear l K₀ hl c E

/-- The specified source composite on integral representatives.
Source: blueprint FrEx source (blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelSource := modelFunctor l K₀ hl f gX gY M E ⋙ constructibleIntegralPullback l E gY

/-- The specified target composite on integral representatives.
Source: blueprint FrEx target (blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelTarget := constructibleIntegralPullback l E gX ⋙ modelFunctor l K₀ hl f gX gY M E

/-- Linearity of the complete source composite, with its actual constant action.
Source: blueprint scalar-localization paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: modelLinear and pullback_linear supply additive O_E-linear factors;
composition preserves both structures and their specified constant actions. -/
theorem modelSource_linear :
    (modelSource l K₀ hl f gX gY M E).Additive ∧
      (modelSource l K₀ hl f gX gY M E).Linear (Padic.coefficientExtensionIntegers l E) := by
  let := (modelLinear l K₀ hl f gX gY M E).1
  let := (modelLinear l K₀ hl f gX gY M E).2
  let := (pullback_linear l E Y gY).1
  let := (pullback_linear l E Y gY).2
  dsimp only [modelSource]
  exact ⟨inferInstance, inferInstance⟩

/-- Linearity of the complete target composite, in the prescribed opposite order.
Source: blueprint scalar-localization paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: pullback_linear followed by modelLinear gives the additive O_E-linear
composition on the target, with exactly the same constant coefficient action. -/
theorem modelTarget_linear :
    (modelTarget l K₀ hl f gX gY M E).Additive ∧
      (modelTarget l K₀ hl f gX gY M E).Linear (Padic.coefficientExtensionIntegers l E) := by
  let := (modelLinear l K₀ hl f gX gY M E).1
  let := (modelLinear l K₀ hl f gX gY M E).2
  let := (pullback_linear l E X gX).1
  let := (pullback_linear l E X gX).2
  dsimp only [modelTarget]
  exact ⟨inferInstance, inferInstance⟩

/-- The rational operation uses the recorded compact-support functor at the retained c.
The direct-image case is literal localization of its constructed integral action.
Source: blueprint rational coefficient passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelRationalFunctor :
    sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E Y :=
  match M with
  | .direct _ =>
    letI := (directImage_linear l E K₀ hl f).1
    letI := (directImage_linear l E K₀ hl f).2
    localizedFunctor l E (directImageFunctor l E K₀ hl f)
  | .compact c _ _ _ => sfCompactSupportFiniteFunctor l K₀ hl c E

/-- The rational source, with the recorded rational operations.
Source: blueprint rational paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelRationalSource :=
  modelRationalFunctor l K₀ hl f gX gY M E ⋙ rationalDerivedPullback l E gY

/-- The rational target, in the specified opposite order.
Source: blueprint rational paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelRationalTarget :=
  rationalDerivedPullback l E gX ⋙ modelRationalFunctor l K₀ hl f gX gY M E

/-- Raw localization of the integral source is the recorded rational source.
Source: blueprint rational paragraph; def-weil-rationalization-karoubi
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: the compact branch uses precisely sfCompactSupportFiniteIntegralFunctor.
Its localization has the same objects and baseChange Hom map as
sfCompactSupportFiniteFunctor. For direct image this is the definition. Use the
pure-tensor normalization of rationalDerivedPullback and composition on pure
tensors; tensor induction and functor extensionality give equality on all maps. -/
theorem modelRationalSource_eq :
    letI := (modelSource_linear l K₀ hl f gX gY M E).1
    letI := (modelSource_linear l K₀ hl f gX gY M E).2
    localizedFunctor l E (modelSource l K₀ hl f gX gY M E) =
      modelRationalSource l K₀ hl f gX gY M E := by
  let := (modelLinear l K₀ hl f gX gY M E).1
  let := (modelLinear l K₀ hl f gX gY M E).2
  let := (pullback_linear l E Y gY).1
  let := (pullback_linear l E Y gY).2
  dsimp only [modelSource, modelRationalSource]
  rw [localizedFunctor_comp, localizedPullback_eq]
  cases M with
  | direct w => rfl
  | compact c gB wp sj => rfl

/-- The same literal localization identity for the target composite.
Source: blueprint rational paragraph; def-weil-rationalization-karoubi
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: use the preceding pure-tensor computation in the opposite functor order.
The retained c and the integral object representatives are the same; only the
order of the two actual tensor Hom maps changes. Tensor induction proves the
identity on every Hom, and functor extensionality concludes. -/
theorem modelRationalTarget_eq :
    letI := (modelTarget_linear l K₀ hl f gX gY M E).1
    letI := (modelTarget_linear l K₀ hl f gX gY M E).2
    localizedFunctor l E (modelTarget l K₀ hl f gX gY M E) =
      modelRationalTarget l K₀ hl f gX gY M E := by
  let := (modelLinear l K₀ hl f gX gY M E).1
  let := (modelLinear l K₀ hl f gX gY M E).2
  let := (pullback_linear l E X gX).1
  let := (pullback_linear l E X gX).2
  dsimp only [modelTarget, modelRationalTarget]
  rw [localizedFunctor_comp, localizedPullback_eq]
  cases M with
  | direct w => rfl
  | compact c gB wp sj => rfl

attribute [local irreducible] modelRationalFunctor

/-- Rational exchange is the literal image of the integral exchange, expressed
on the recorded rational compact-support functor in its compact branch.
Source: blueprint rational paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelRationalExchange : modelRationalSource l K₀ hl f gX gY M E ⟶
    modelRationalTarget l K₀ hl f gX gY M E :=
  letI := (modelSource_linear l K₀ hl f gX gY M E).1
  letI := (modelSource_linear l K₀ hl f gX gY M E).2
  letI := (modelTarget_linear l K₀ hl f gX gY M E).1
  letI := (modelTarget_linear l K₀ hl f gX gY M E).2
  (eqToIso (modelRationalSource_eq l K₀ hl f gX gY M E)).inv ≫
    localizedTransformation l E (modelSource l K₀ hl f gX gY M E)
      (modelTarget l K₀ hl f gX gY M E) (modelExchange l K₀ hl f gX gY M E) ≫
    (eqToIso (modelRationalTarget_eq l K₀ hl f gX gY M E)).hom

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The actual completed integral coefficient extension used by the stage system.
Source: def-weil-algebraically-closed-coefficients
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
abbrev scalar (T : Scheme.{u}) := sfConstructibleIntegralScalarExtension 0 l
  (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι T

section PullScalarNaturality
universe u₁ v₁
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] integralDerivedPullback integralScalarExtension
  scalarPullbackOrdinary

private theorem scalar_conjugation_naturality {C : Type u₁} [Category.{v₁} C]
    {A B A' B' D E D' E' : C}
    (c : A ≅ A') (c' : B ≅ B') (d : D ≅ D') (d' : E ≅ E')
    (p : A ⟶ B) (p' : A' ⟶ B') (q : D ⟶ E) (q' : D' ⟶ E')
    (e : A ≅ D) (e' : B ≅ E)
    (hc : p ≫ c'.hom = c.hom ≫ p')
    (hd : q ≫ d'.hom = d.hom ≫ q')
    (he : p ≫ e'.hom = e.hom ≫ q) :
    p' ≫ (c'.inv ≫ e'.hom ≫ d'.hom) =
      (c.inv ≫ e.hom ≫ d.hom) ≫ q' := by
  apply (cancel_epi c.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← hc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, he, Category.assoc, hd]

/-- The pullback scalar comparison is fixed at every object by the recorded
K-flat normalized comparison, rather than an arbitrary natural isomorphism.
Source: def-weil-derived-pullback-tensor-hom, scalar comparison
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: integralPullbackScalarComparison is induced by the balanced tensor chain
map on the single K-flat quotient system. It is natural on complexes and roofs.
Its components determine the natural isomorphism uniquely. -/
theorem pullScalar_existsUnique (T : Scheme.{u})
    [∀ t : T, Invertible (l : T.residueField t)] (g : T ⟶ T) :
    ∃! b : constructibleIntegralPullback l E g ⋙ scalar l E L ι T ≅
      scalar l E L ι T ⋙ constructibleIntegralPullback l L g,
      ∀ K, b.app K = integralPullbackScalarComparison l E L ι g K := by
  refine ⟨NatIso.ofComponents (fun K ↦ integralPullbackScalarComparison l E L ι g K)
    ?_, fun K ↦ rfl, ?_⟩
  · intro K M a
    apply ObjectProperty.hom_ext
    change (integralScalarExtension l E L ι T).map
        ((integralDerivedPullback l E g).map a.hom) ≫
          (scalarPullbackCompleted l E L ι g M.obj M.property.1
            ((constructibleIntegralPullback l E g).obj M).property.1).hom =
      (scalarPullbackCompleted l E L ι g K.obj K.property.1
        ((constructibleIntegralPullback l E g).obj K).property.1).hom ≫
        (integralDerivedPullback l L g).map
          ((integralScalarExtension l E L ι T).map a.hom)
    dsimp only [scalarPullbackCompleted, Iso.trans_hom, Functor.mapIso_hom]
    have hnX := (scalarCompletion l E L ι T).naturality
      ((integralDerivedPullback l E g).map a.hom)
    have hnY := (scalarCompletion l E L ι T).naturality a.hom
    have hnO := (scalarPullbackOrdinary l E L ι g).hom.naturality a.hom
    dsimp only [Functor.comp_map] at hnO
    exact scalar_conjugation_naturality
      (scalarCompletionIso l E L ι T _
        ((constructibleIntegralPullback l E g).obj K).property.1)
      (scalarCompletionIso l E L ι T _
        ((constructibleIntegralPullback l E g).obj M).property.1)
      ((integralDerivedPullback l L g).mapIso
        (scalarCompletionIso l E L ι T K.obj K.property.1))
      ((integralDerivedPullback l L g).mapIso
        (scalarCompletionIso l E L ι T M.obj M.property.1))
      _ _ _ _
      ((scalarPullbackOrdinary l E L ι g).app K.obj)
      ((scalarPullbackOrdinary l E L ι g).app M.obj)
      hnX
      (by
        set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
        simpa only [Functor.mapIso_hom, scalarCompletionIso, asIso_hom,
          Functor.map_comp] using
          congrArg (integralDerivedPullback l L g).map hnY)
      hnO
  · intro b hb
    ext K
    exact congrArg (fun i ↦ i.hom.hom) (hb K)

end PullScalarNaturality

attribute [local irreducible] constructibleIntegralPullback

/-- The specified integral pullback scalar comparison.
Source: blueprint coefficient passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def pullScalar (T : Scheme.{u}) [∀ t : T, Invertible (l : T.residueField t)] (g : T ⟶ T) :=
  (pullScalar_existsUnique l E L ι T g).exists.choose

attribute [local irreducible] pullScalar

/-- The coefficient mate for the recorded integral compact-support functor,
conjugated by the projection-normalized system identifications at E and L.
Source: lem-fix-operation-reduction, compact-support coefficient passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def compactCoefficientExchange (c : Compactification f) :
    sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι ⋙ integralScalarExtensionOfUniverses l E L ι Y ⟶
      scalar l E L ι X ⋙ sfCompactSupportFiniteIntegralFunctor l K₀ hl c L ⋙
        (sfIntegralConstructible l L Y).ι :=
  whiskerRight (compactRealization l E K₀ hl f c).hom
      (integralScalarExtensionOfUniverses l E L ι Y) ≫
    coefficientExchange l E L ι
      (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g)
      (systemDerivedOpen l L c.i ⋙ systemDirect l L c.g)
      (systemCompactScalar l E L ι c) ≫
    whiskerLeft (scalar l E L ι X) (compactRealization l L K₀ hl f c).inv

/-- Coefficient change of the selected operation is the constructed whole-system mate.
Source: lem-fix-operation-reduction; blueprint coefficient passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelScalarMap : modelFunctor l K₀ hl f gX gY M E ⋙ scalar l E L ι Y ⟶
    scalar l E L ι X ⋙ modelFunctor l K₀ hl f gX gY M L := by
  cases M with
  | direct _w =>
    exact
      { app := fun K ↦ ObjectProperty.homMk
          ((coefficientExchange l E L ι (systemDirect l E f) (systemDirect l L f)
            (systemDirectScalar l E L ι f)).app K)
        naturality := fun _K _N a ↦ ObjectProperty.hom_ext _
          ((coefficientExchange l E L ι (systemDirect l E f) (systemDirect l L f)
            (systemDirectScalar l E L ι f)).naturality a) }
  | compact c _gB _wp _sj =>
    exact
      { app := fun K ↦ ObjectProperty.homMk
          ((compactCoefficientExchange l K₀ hl f E L ι c).app K)
        naturality := fun _K _N a ↦ ObjectProperty.hom_ext _
          ((compactCoefficientExchange l K₀ hl f E L ι c).naturality a) }

include hl xo yo xft xqc yft yqc fo ix iy in
/-- Finite coefficient extension makes this actual integral mate invertible.
Source: lem-fix-operation-reduction; finite-free completed scalar comparison
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: the finite integral coefficient extension is finite free. Its ordinary
tensor is a finite direct sum locally on coefficients and commutes with direct
image, exact open extension and total derived inverse limit on these complete
constructible inputs. The balanced tensor identifications on simultaneous
K-flat and K-injective representatives identify the inverse with the displayed
mate. This proves invertibility of that constructed map, also for ramification;
no global flatness of the finite quotient-ring inclusion is asserted. -/
theorem modelScalarMap_isIso : IsIso (modelScalarMap l K₀ hl f gX gY M E L ι) := by
  let (K : sfIntegralConstructibleCategory l E X) :
      IsIso ((modelScalarMap l K₀ hl f gX gY M E L ι).app K) := by
    cases M with
    | direct w =>
      apply (ObjectProperty.isIso_hom_iff _).mp
      exact directImageCoefficientExchange_isIso l K₀ hl (f := f) E L ι K
    | compact c gB wp sj =>
      apply (ObjectProperty.isIso_hom_iff _).mp
      change IsIso ((compactCoefficientExchange l K₀ hl f E L ι c).app K)
      exact
        ((integralScalarExtensionOfUniverses l E L ι Y).mapIso
            ((compactRealization l E K₀ hl f c).app K) ≪≫
          @asIso _ _ _ _ ((coefficientExchange l E L ι
            (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g)
            (systemDerivedOpen l L c.i ⋙ systemDirect l L c.g)
            (systemCompactScalar l E L ι c)).app K)
            (sfCompactSupportCoefficientExchange_isIso l K₀ hl c E L ι K) ≪≫
          ((compactRealization l L K₀ hl f c).app ((scalar l E L ι X).obj K)).symm).isIso_hom
  exact NatIso.isIso_of_isIso_app _

/-- The actual integral operation scalar isomorphism.
Source: blueprint coefficient passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelScalar :=
  letI := modelScalarMap_isIso l K₀ hl f gX gY M E L ι
  asIso (modelScalarMap l K₀ hl f gX gY M E L ι)

attribute [local irreducible] modelScalarMap

/-- Scalar comparison for the source composite, in its prescribed order.
Source: blueprint coefficient passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelSourceScalar : modelSource l K₀ hl f gX gY M E ⋙ scalar l E L ι Y ≅
    scalar l E L ι X ⋙ modelSource l K₀ hl f gX gY M L :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (modelFunctor l K₀ hl f gX gY M E) (pullScalar l E L ι Y gY) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (modelScalar l K₀ hl f gX gY M E L ι)
      (constructibleIntegralPullback l L gY) ≪≫
    Functor.associator _ _ _

/-- Scalar comparison for the target composite, in its prescribed order.
Source: blueprint coefficient passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelTargetScalar : modelTarget l K₀ hl f gX gY M E ⋙ scalar l E L ι Y ≅
    scalar l E L ι X ⋙ modelTarget l K₀ hl f gX gY M L :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (constructibleIntegralPullback l E gX) (modelScalar l K₀ hl f gX gY M E L ι) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (pullScalar l E L ι X gX) (modelFunctor l K₀ hl f gX gY M L) ≪≫
    Functor.associator _ _ _

/-- Select source or target while retaining its prescribed integral comparison.
Source: blueprint common-stage passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelSideScalar (target : Bool) :
    (if target then modelTarget l K₀ hl f gX gY M E
      else modelSource l K₀ hl f gX gY M E) ⋙ scalar l E L ι Y ≅
    scalar l E L ι X ⋙ (if target then modelTarget l K₀ hl f gX gY M L
      else modelSource l K₀ hl f gX gY M L) := by
  cases target with
  | false => exact modelSourceScalar l K₀ hl f gX gY M E L ι
  | true => exact modelTargetScalar l K₀ hl f gX gY M E L ι

attribute [local irreducible] modelFunctor modelSource modelTarget
  modelRationalSource modelRationalTarget modelRationalExchange modelScalar
  modelSourceScalar modelTargetScalar

private theorem localizedScalarIso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X Y : Scheme.{u})
    (F : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y)
    [F.Additive] [F.Linear (Padic.coefficientExtensionIntegers l E)]
    (G : sfIntegralConstructibleCategory l L X ⥤ sfIntegralConstructibleCategory l L Y)
    [G.Additive] [G.Linear (Padic.coefficientExtensionIntegers l L)]
    (e : F ⋙ scalar l E L ι Y ≅ scalar l E L ι X ⋙ G) :
    ∃! b : localizedFunctor l E F ⋙ sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ≅
        sfRationalScalarExtension l E X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙ localizedFunctor l L G,
      ∀ K : sfRationalConstructibleCategory l E X,
        HEq (b.hom.app K) ((sfRationalConstructibleLocalization l L Y).map
          (e.hom.app K.obj)) := by
  have : (localizedFunctor l E F).Additive :=
    ⟨fun {K N a b} ↦ (localizedHom l E F K N).map_add a b⟩
  have : (localizedFunctor l L G).Additive :=
    ⟨fun {K N a b} ↦ (localizedHom l L G K N).map_add a b⟩
  have hX := (sfRationalScalarExtension_existsUnique l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec
  have hY := (sfRationalScalarExtension_existsUnique l E Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec
  let ψ a := (sfRationalCoefficientEquiv l L).symm (ι (sfRationalCoefficientEquiv l E a))
  apply localizedIso
    (Padic.coefficientExtensionUniformizer l E) (Padic.coefficientExtensionUniformizer l L)
    ψ (F ⋙ scalar l E L ι Y) (scalar l E L ι X ⋙ G) e
    (localizedFunctor l E F ⋙ sfRationalScalarExtension l E Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι)
    (sfRationalScalarExtension l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙ localizedFunctor l L G)
  · intro K
    exact hY.2.1 _
  · intro K
    exact congrArg (localizedFunctor l L G).obj (hX.2.1 K)
  · intro K N a c
    exact hY.2.2 (F.obj K) (F.obj N) (F.map a) c
  · intro K N a c
    have hm := map_heq (localizedFunctor l L G)
      (hX.2.1 ⟨K⟩) (hX.2.1 ⟨N⟩) (hX.2.2 K N a c)
    exact hm.trans (heq_of_eq (LinearMap.baseChange_tmul _ _ _))

/-- Rational scalar comparison fixed by localization of the already constructed
integral scalar maps, on both source and target composites.
Source: blueprint common-stage passage
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: localize each specified integral component. The pure tensor scalar-action
formula proves naturality for every rational Hom. Its inverse localizes as well.
The component formula determines the comparison uniquely. -/
theorem modelRationalScalar_existsUnique (target : Bool) :
    let R := if target then modelRationalTarget l K₀ hl f gX gY M E
      else modelRationalSource l K₀ hl f gX gY M E
    let R' := if target then modelRationalTarget l K₀ hl f gX gY M L
      else modelRationalSource l K₀ hl f gX gY M L
    ∃! b : R ⋙ sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ≅
        sfRationalScalarExtension l E X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙ R',
      ∀ K : sfRationalConstructibleCategory l E X,
        HEq (b.hom.app K) ((sfRationalConstructibleLocalization l L Y).map
          ((modelSideScalar l K₀ hl f gX gY M E L ι target).hom.app K.obj)) := by
  cases target with
  | false =>
    let := (modelSource_linear l K₀ hl f gX gY M E).1
    let := (modelSource_linear l K₀ hl f gX gY M E).2
    let := (modelSource_linear l K₀ hl f gX gY M L).1
    let := (modelSource_linear l K₀ hl f gX gY M L).2
    dsimp only [Bool.false_eq_true, ↓reduceIte]
    rw [← modelRationalSource_eq, ← modelRationalSource_eq]
    exact localizedScalarIso l E L ι X Y _ _ (modelSourceScalar l K₀ hl f gX gY M E L ι)
  | true =>
    let := (modelTarget_linear l K₀ hl f gX gY M E).1
    let := (modelTarget_linear l K₀ hl f gX gY M E).2
    let := (modelTarget_linear l K₀ hl f gX gY M L).1
    let := (modelTarget_linear l K₀ hl f gX gY M L).2
    dsimp only [↓reduceIte]
    rw [← modelRationalTarget_eq, ← modelRationalTarget_eq]
    exact localizedScalarIso l E L ι X Y _ _ (modelTargetScalar l K₀ hl f gX gY M E L ι)

/-- The normalized rational comparison, retaining the whole-system integral mate.
Source: blueprint common-stage passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelRationalScalar (target : Bool) :=
  (modelRationalScalar_existsUnique l K₀ hl f gX gY M E L ι target).exists.choose

end CoefficientDescent

attribute [irreducible] modelRationalSource modelRationalTarget modelRationalExchange
  modelFunctor modelSource modelTarget modelScalar modelSourceScalar modelTargetScalar
  modelRationalScalar

attribute [local irreducible] modelSideScalar

section CommonStage
attribute [local instance 10000] AlgebraicallyClosedCoefficients.coefficientFinite
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (gX : X ⟶ X) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY] (M : SupportModel f gX gY)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The prescribed rational source or target at the actual finite coefficient stage.
Source: blueprint common-stage passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def stageSide (target : Bool) (E : Index l Ω) : Stage l Ω X E ⥤ Stage l Ω Y E :=
  if target then modelRationalTarget l K₀ hl f gX gY M (Coefficient.{u} l Ω E)
    else modelRationalSource l K₀ hl f gX gY M (Coefficient.{u} l Ω E)

attribute [local irreducible] operationStageTransitionIso

/-- The actual beta: whole-system coefficient mate, localized, then expressed in
the recorded stage-system transitions. No comparison is supplied as an input.
Source: blueprint common-stage passage; prop-weil-pbc-descent-functors
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def stageBeta (target : Bool) {E L : Index l Ω} (h : E ≤ L) :
    stageSide l K₀ hl f gX gY M Ω target E ⋙ (stageSystem l Ω Y).T h ≅
      (stageSystem l Ω X).T h ⋙ stageSide l K₀ hl f gX gY M Ω target L :=
  isoWhiskerLeft (stageSide l K₀ hl f gX gY M Ω target E)
      (operationStageTransitionIso l Ω Y E L h) ≪≫
    modelRationalScalar l K₀ hl f gX gY M (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) target ≪≫
    isoWhiskerRight (operationStageTransitionIso l Ω X E L h).symm
      (stageSide l K₀ hl f gX gY M Ω target L)

attribute [local irreducible] stageBeta

/-- The specified scalar comparisons obey the full coefficient-tower cocycle,
including repeated fields and the identity coefficient embedding.
Source: lem-fix-operation-reduction; Stacks 06YY, 0941
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: at the system level both scalar chains are the same balanced tensor map
on each simultaneous K-flat representative. The normalized pullback and ordinary
section-direct-image compositors preserve this map. Mate pasting proves the
corresponding direct-image and open-adjunction identities. The actual system
counits and total-limit functor preserve the identities. Localize those exact
maps, and cancel the stage transition identifications. This is precisely the
displayed cocycle with the recorded scalar associators. -/
theorem stageBeta_coherence (target : Bool) (E L N : Index l Ω)
    (h : E ≤ L) (k : L ≤ N) (K : Stage l Ω X E) :
    ((stageSystem l Ω Y).T k).map
        ((stageBeta l K₀ hl f gX gY M Ω target h).hom.app K) ≫
      (stageBeta l K₀ hl f gX gY M Ω target k).hom.app
        (((stageSystem l Ω X).T h).obj K) ≫
      (stageSide l K₀ hl f gX gY M Ω target N).map
        (((stageSystem l Ω X).assoc h k).hom.app K) =
    ((stageSystem l Ω Y).assoc h k).hom.app
        ((stageSide l K₀ hl f gX gY M Ω target E).obj K) ≫
      (stageBeta l K₀ hl f gX gY M Ω target (h.trans k)).hom.app K := by
  sorry

/-- The coherent family uses the explicit beta just constructed, so the induced
common-stage operation has the canonical representative formula.
Source: prop-weil-pbc-descent-functors
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def stageAction (target : Bool) :
    StageSystem.Morphism (stageSystem l Ω X) (stageSystem l Ω Y) where
  Φ := stageSide l K₀ hl f gX gY M Ω target
  β h := stageBeta l K₀ hl f gX gY M Ω target h
  coh h k K := stageBeta_coherence l K₀ hl f gX gY M Ω target _ _ _ h k K

/-- The constructed exchanges commute with the constructed canonical scalar betas.
Source: lem-fix-operation-reduction; prop-weil-pbc-descent-functors
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: expand the system exchange and coefficient comparison into their actual
pullback-composition maps, units and counits. The normalized scalar/pullback
associator commutes with the Frobenius square. Naturality and mate pasting give
the coefficient square in the derived category of whole systems. The same
calculation for the inverse open mate proves the compact-support square, keeping
the same c. Apply exact scalar restriction and total inverse limit to this
identity, compose with the specified alpha and beta, and localize. This yields
the equation below before passing to common-stage morphism classes. -/
theorem stageExchange_compatible (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E) :
    ((stageSystem l Ω Y).T h).map
        ((modelRationalExchange l K₀ hl f gX gY M (Coefficient.{u} l Ω E)).app K) ≫
      (stageBeta l K₀ hl f gX gY M Ω true h).hom.app K =
    (stageBeta l K₀ hl f gX gY M Ω false h).hom.app K ≫
      (modelRationalExchange l K₀ hl f gX gY M (Coefficient.{u} l Ω L)).app
        (((stageSystem l Ω X).T h).obj K) := by
  sorry

/-- The compatible exchange family is fixed at every finite stage by its
localized integral component.
Source: prop-weil-pbc-descent-functors
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def stageExchange : StageSystem.Morphism.Hom
    (stageAction l K₀ hl f gX gY M Ω false) (stageAction l K₀ hl f gX gY M Ω true) where
  τ E := modelRationalExchange l K₀ hl f gX gY M (Coefficient.{u} l Ω E)
  comm h K := stageExchange_compatible l K₀ hl f gX gY M Ω _ _ h K

/-- The common-stage Frobenius exchange: at (E,K) its component is exactly the
morphism class of the rational exchange at E. Its naturality includes every
common-stage representative by the existing descent construction. No Karoubi
completion and no finite reduction of a rational object occur.
Source: blueprint common-stage paragraphs; prop-weil-pbc-descent-functors
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def commonStageExchange :
    (stageAction l K₀ hl f gX gY M Ω false).functor ⟶
      (stageAction l K₀ hl f gX gY M Ω true).functor :=
  StageSystem.Morphism.descNatTrans (stageExchange l K₀ hl f gX gY M Ω)

end CommonStage

end WeilConjectures.FrobeniusExchange
