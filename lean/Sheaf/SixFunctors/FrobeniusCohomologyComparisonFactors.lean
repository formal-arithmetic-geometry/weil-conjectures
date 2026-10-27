/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.SixFunctors.FrobeniusCohomologyRealization

/-! # Canonical factors of the cohomology coefficient comparison

Source: Deligne, Weil II (1.1.1)(d), (1.1.14), coefficient extension and cohomology
(blueprint: def-weil-frobenius-cohomology-comparison-factors).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w x y z u'

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures
namespace CohomologyRealization
open AlgebraicallyClosedCoefficients (Index)
open GeneralAlgebraicallyClosedCoefficients (stageSystem)

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard

set_option allowUnsafeReducibility true in
attribute [local irreducible] frobeniusCohomologyCoefficientExtension
  frobeniusCohomologyRationalFunctor frobeniusCohomologyRationalScalar
  operationStageTransitionIso frobeniusCoefficientTower DerivedCategory.fieldScalarTower

open AlgebraicallyClosedCoefficients (Coefficient coefficientInclusion coefficientInclusion_laws)

/-- The canonical field-scalar associator with an equality of composite maps.
Source: Deligne, Weil II (1.1.1)(d), iterated coefficient extension
(blueprint: def-weil-frobenius-cohomology-comparison-factors). -/
def scalarAssociator {F G H : Type u} [Field F] [Field G] [Field H]
    (φ : F →+* G) (ψ : G →+* H) (θ : F →+* H) (h : ψ.comp φ = θ) :
    DerivedCategory.fieldDerivedScalarExtension φ ⋙
        DerivedCategory.fieldDerivedScalarExtension ψ ≅
      DerivedCategory.fieldDerivedScalarExtension θ :=
  DerivedCategory.fieldScalarTower φ ψ ≪≫
    eqToIso (congrArg DerivedCategory.fieldDerivedScalarExtension h)

/-- The canonical scalar-and-size comparison with an equality of embeddings.
Source: Deligne, Weil II (1.1.1)(d), iterated coefficient extension
(blueprint: def-weil-frobenius-cohomology-comparison-factors). -/
def coefficientRingComparison {F G : Type u} [Field F] [Field G]
    {Ω : Type v} [Field Ω] (φ : F →+* G) (ψ : G →+* Ω) (χ : F →+* Ω)
    (h : ψ.comp φ = χ) :
    DerivedCategory.fieldDerivedScalarExtension φ ⋙
        frobeniusCohomologyCoefficientExtension ψ ≅
      frobeniusCohomologyCoefficientExtension χ :=
  frobeniusCoefficientTower φ ψ ≪≫
    eqToIso (congrArg frobeniusCohomologyCoefficientExtension h)

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The actual scalar-and-size functor into D(Ω).
Source: Deligne, Weil II (1.1.1)(d), coefficient extension
(blueprint: def-weil-frobenius-cohomology-comparison-factors). -/
abbrev coefficient (E : Index l Ω) :=
  frobeniusCohomologyCoefficientExtension (frobeniusCohomologyStageEmbedding.{u, v} l Ω E)

/-- The derived scalar associator, including the equality of coefficient inclusions.
Source: Deligne, Weil II (1.1.1)(d), coefficient extension
(blueprint: def-weil-frobenius-cohomology-comparison-factors). -/
def fieldAssociator (E L N : Index l Ω) (h : E ≤ L) (k : L ≤ N) :
    DerivedCategory.fieldDerivedScalarExtension (coefficientInclusion.{u} l Ω E L h).toRingHom ⋙
        DerivedCategory.fieldDerivedScalarExtension
          (coefficientInclusion.{u} l Ω L N k).toRingHom ≅
      DerivedCategory.fieldDerivedScalarExtension
        (coefficientInclusion.{u} l Ω E N (h.trans k)).toRingHom :=
  scalarAssociator
    (coefficientInclusion.{u} l Ω E L h).toRingHom
    (coefficientInclusion.{u} l Ω L N k).toRingHom
    (coefficientInclusion.{u} l Ω E N (h.trans k)).toRingHom
    (congrArg AlgHom.toRingHom ((coefficientInclusion_laws l Ω).2 E L N h k))

/-- The specified balanced tensor comparison followed by the embedding equality.
Source: Deligne, Weil II (1.1.1)(d), coefficient extension
(blueprint: def-weil-frobenius-cohomology-comparison-factors). -/
def coefficientComparison (E L : Index l Ω) (h : E ≤ L) :
    DerivedCategory.fieldDerivedScalarExtension (coefficientInclusion.{u} l Ω E L h).toRingHom ⋙
        coefficient.{u, v} l Ω L ≅ coefficient.{u, v} l Ω E :=
  coefficientRingComparison (coefficientInclusion.{u} l Ω E L h).toRingHom
    (frobeniusCohomologyStageEmbedding.{u, v} l Ω L)
    (frobeniusCohomologyStageEmbedding.{u, v} l Ω E)
    (frobeniusCohomologyStageEmbedding_comp l Ω E L h)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom] (c₀ : Compactification Y₀.hom) (compact : Bool)

/-- Rational cohomology before the final extension to Ω, included in D(E).
Source: Deligne, Weil II (1.1.14), cohomology realization
(blueprint: def-weil-frobenius-cohomology-comparison-factors). -/
def rationalStage (E : Index l Ω) :
    GeneralAlgebraicallyClosedCoefficients.Stage l Ω (D.geometricFiber Y₀).left E ⥤
      @DerivedCategory (ModuleCat.{u} (Coefficient.{u} l Ω E)) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian.{u} _) := by
  letI : Algebra ℚ_[l] (Coefficient.{u} l Ω E) :=
    inferInstanceAs (Algebra ℚ_[l] (Shrink.{u} E.val))
  exact frobeniusCohomologyRationalFunctor D l hl (Coefficient.{u} l Ω E) Y₀ c₀ compact ⋙
    (DerivedCategory.pointFiniteDimensional (Coefficient.{u} l Ω E)).ι

/-- The prescribed rational scalar mate, expressed using the recorded stage transition.
Source: Deligne, Weil II (1.1.14), cohomology realization
(blueprint: def-weil-frobenius-cohomology-comparison-factors). -/
def rationalComparison (E L : Index l Ω) (h : E ≤ L) :
    rationalStage l Ω D hl Y₀ c₀ compact E ⋙
        DerivedCategory.fieldDerivedScalarExtension
          (coefficientInclusion.{u} l Ω E L h).toRingHom ≅
      (stageSystem l Ω (D.geometricFiber Y₀).left).T h ⋙
        rationalStage l Ω D hl Y₀ c₀ compact L :=
  Functor.isoWhiskerRight
      (frobeniusCohomologyRationalScalar D l hl (Coefficient.{u} l Ω E) Y₀ c₀ compact
        (Coefficient.{u} l Ω L) (coefficientInclusion.{u} l Ω E L h))
      (DerivedCategory.pointFiniteDimensional (Coefficient.{u} l Ω L)).ι ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (operationStageTransitionIso l Ω (D.geometricFiber Y₀).left
        E L h).symm
        (frobeniusCohomologyRationalFunctor D l hl (Coefficient.{u} l Ω L) Y₀ c₀ compact))
      (DerivedCategory.pointFiniteDimensional (Coefficient.{u} l Ω L)).ι

section ComparisonRecords

/-- The specified rational and scalar comparison factors, with their literal category models.
Source: Deligne, Weil II (1.1.1)(d), (1.1.14), iterated coefficient extension
(blueprint: def-weil-frobenius-cohomology-comparison-factors). -/
structure CoefficientData
    {I : Type u'} [Preorder I]
    {B : I → Type w} [bCategory : ∀ i, Category.{x} (B i)]
    {D : Type y} [Category.{z} D] where
  A : ∀ i, B i ⥤ D
  F : ∀ (i j : I), i ≤ j → B i ⥤ B j
  c : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k), F i j h ⋙ F j k h' ≅ F i k (h.trans h')
  p : ∀ (i j : I) (h : i ≤ j), F i j h ⋙ A j ≅ A i

/-- Rational cohomology comparisons over the separately constructed coefficient data.
Source: Deligne, Weil II (1.1.1)(d), (1.1.14), iterated coefficient extension
(blueprint: def-weil-frobenius-cohomology-comparison-factors). -/
structure FactorData
    {I : Type u'} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
    {B : I → Type w} [bCategory : ∀ i, Category.{x} (B i)]
    {D : Type y} [Category.{z} D] (S : StageSystem C)
    extends CoefficientData (B := B) (D := D) where
  H : ∀ i, C i ⥤ B i
  q : ∀ (i j : I) (h : i ≤ j), H i ⋙ F i j h ≅ S.T h ⋙ H j


variable {I : Type u'} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  {B : I → Type w} [bCategory : ∀ i, Category.{x} (B i)]
  {D : Type y} [Category.{z} D] {S : StageSystem C}


/-- Compose the rational stage and the scalar-and-size extension.
Source: Deligne, Weil II (1.1.1)(d), (1.1.14), iterated coefficient extension
(blueprint: def-weil-frobenius-cohomology-comparison-factors). -/
def factorDataStage (d : FactorData (B := B) (D := D) S) (i : I) : C i ⥤ D :=
  d.H i ⋙ d.A i


/-- The comparison of the composite realizations, with explicit functor associators.
Source: Deligne, Weil II (1.1.1)(d), (1.1.14), iterated coefficient extension
(blueprint: def-weil-frobenius-cohomology-comparison-factors). -/
def factorDataComparison (d : FactorData (B := B) (D := D) S)
    (i j : I) (h : i ≤ j) : factorDataStage d i ≅ S.T h ⋙ factorDataStage d j :=
  Functor.isoWhiskerLeft (d.H i) (d.p i j h).symm ≪≫
    (Functor.associator (d.H i) (d.F i j h) (d.A j)).symm ≪≫
    Functor.isoWhiskerRight (d.q i j h) (d.A j) ≪≫
    Functor.associator (S.T h) (d.H j) (d.A j)


/-- The rational tower equation, before the final extension of coefficients.
Source: Deligne, Weil II (1.1.1)(d), (1.1.14), iterated coefficient extension
(blueprint: def-weil-frobenius-cohomology-comparison-factors). -/
def factorRationalCocycle (d : FactorData (B := B) (D := D) S) : Prop :=
  ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k) (K : C i),
    (d.F j k h').map ((d.q i j h).hom.app K) ≫
      (d.q j k h').hom.app ((S.T h).obj K) ≫ (d.H k).map ((S.assoc h h').hom.app K) =
    (d.c i j k h h').hom.app ((d.H i).obj K) ≫ (d.q i k (h.trans h')).hom.app K


/-- The balanced tensor tower equation for the final coefficient extension.
Source: Deligne, Weil II (1.1.1)(d), (1.1.14), iterated coefficient extension
(blueprint: def-weil-frobenius-cohomology-comparison-factors). -/
def factorCoefficientCocycle (d : CoefficientData (B := B) (D := D)) : Prop :=
  ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
    Functor.isoWhiskerRight (d.c i j k h h') (d.A k) ≪≫ d.p i k (h.trans h') =
      Functor.associator (d.F i j h) (d.F j k h') (d.A k) ≪≫
        Functor.isoWhiskerLeft (d.F i j h) (d.p j k h') ≪≫ d.p i j h

/-- The component form of the coefficient comparison equation.
Source: Deligne, Weil II (1.1.1)(d), iterated coefficient extension
(blueprint: def-weil-frobenius-cohomology-comparison-factors).

Proof: apply the hom component at V to the natural-isomorphism equation and
simplify the identity component of the functor associator. -/
theorem factorCoefficientCocycle_app (d : CoefficientData (B := B) (D := D))
    (hc : factorCoefficientCocycle d) (i j k : I) (h : i ≤ j) (h' : j ≤ k)
    (V : B i) :
    (d.A k).map ((d.c i j k h h').hom.app V) ≫ (d.p i k (h.trans h')).hom.app V =
      (d.p j k h').hom.app ((d.F i j h).obj V) ≫ (d.p i j h).hom.app V := by
  have he := congrArg (fun e ↦ e.hom.app V) (hc i j k h h')
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] using he

/-- Bundle constructed coefficient comparisons with their proved natural-isomorphism equation.
Source: Deligne, Weil II (1.1.1)(d), iterated coefficient extension
(blueprint: def-weil-frobenius-cohomology-comparison-factors). -/
def coefficientDataWithCocycle
    (A : ∀ i, B i ⥤ D) (F : ∀ (i j : I), i ≤ j → B i ⥤ B j)
    (c : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k), F i j h ⋙ F j k h' ≅ F i k (h.trans h'))
    (p : ∀ (i j : I) (h : i ≤ j), F i j h ⋙ A j ≅ A i)
    (hc : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
      Functor.isoWhiskerRight (c i j k h h') (A k) ≪≫ p i k (h.trans h') =
        Functor.associator (F i j h) (F j k h') (A k) ≪≫
          Functor.isoWhiskerLeft (F i j h) (p j k h') ≪≫ p i j h) :
    {d : CoefficientData (B := B) (D := D) // factorCoefficientCocycle d} :=
  ⟨{ A := A, F := F, c := c, p := p }, hc⟩


end ComparisonRecords

/-- The literal small derived category models for an arbitrary family of fields.
Source: Deligne, Weil II (1.1.1)(d), iterated coefficient extension
(blueprint: def-weil-frobenius-cohomology-comparison-factors). -/
abbrev fieldDerivedCategoryFamily {I : Type u'}
    (K : I → Type u) [fieldFamily : ∀ i, Field (K i)] :
    ∀ i, Category.{u} (@DerivedCategory (ModuleCat.{u} (K i)) _ _
      (HasDerivedCategory.ofIsGrothendieckAbelian.{u} _)) :=
  fun _ ↦ inferInstance

/-- The chosen small derived category structures at all finite coefficient stages.
Source: Deligne, Weil II (1.1.1)(d), (1.1.14), iterated coefficient extension
(blueprint: def-weil-frobenius-cohomology-comparison-factors). -/
abbrev coefficientDerivedCategoryFamily
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] :
    ∀ E : Index l Ω, Category.{u}
      (@DerivedCategory (ModuleCat.{u} (AlgebraicallyClosedCoefficients.Coefficient l Ω E))
        _ _ (HasDerivedCategory.ofIsGrothendieckAbelian.{u} _)) :=
  fieldDerivedCategoryFamily (fieldFamily := fun _ ↦ inferInstance)
    (fun E : Index l Ω ↦ AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)


end CohomologyRealization
end WeilConjectures
