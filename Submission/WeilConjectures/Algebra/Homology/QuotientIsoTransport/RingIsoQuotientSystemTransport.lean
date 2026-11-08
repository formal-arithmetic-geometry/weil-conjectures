/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
public import Submission.WeilConjectures.Algebra.Homology.System.SystemDerivedTransition
public import Submission.WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Functor.OfSequence
import Submission.WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
import Submission.WeilConjectures.CategoryTheory.EquivalenceAdjunctionComparison
import all Submission.WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all Submission.WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
import Submission.WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition
import all Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Limits.Final
import all Submission.WeilConjectures.CategoryTheory.Constant.ConstantTowerNormalization
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Submission.WeilConjectures.CategoryTheory.InverseMateEquivalence
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates
import Submission.WeilConjectures.CategoryTheory.Derived.DerivedMateComparison
import Submission.WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Coherent transport of strict quotient systems

Source: def-pur-section-invariant, finite-clopen expansion, steps 2--3 and 5;
Stacks 03D7, 03EK, 015F, 06YY and 07A6
(blueprint: lem-pur-ring-iso-quotient-system-transport).

The structures below spell out the normalization of the equivalence, its scalar
comparisons and its whole-system derived reduction. They are interfaces for this
single theorem. All module categories, restrictions, tensors, adjunctions and
localizations are the recorded library constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance 11000] hasSheafCompose_of_preservesLimitsOfSize
attribute [local instance 11000] SheafOfModules.instPreadditive
attribute [local instance 11000] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance 20000] SheafOfModules.systemEvaluationAdditive
  SheafOfModules.systemEvaluationLimits SheafOfModules.systemEvaluationColimits

attribute [local instance 12000] SheafOfModules.systemRingHasDerived
attribute [local instance 12000] SheafOfModules.strictRingSystemHasDerived
attribute [local instance 12000] SheafOfModules.strictRingSystemAbelian
attribute [local instance 12000] SheafOfModules.instAbelian

namespace SheafOfModules.QuotientIsoTransport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- Use the specified sheafification adjunction directly.
Source: Stacks 03DA (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
theorem moduleWeakSheafify : HasWeakSheafify J AddCommGrpCat.{w} :=
  HasSheafify.isRightAdjoint

attribute [local instance 20000] moduleWeakSheafify

/-- Module sheaves in the coefficient universe, using the recorded category.
Source: Stacks 03DA (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
abbrev Modules (R : Sheaf J CommRingCat.{w}) :=
  ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)

/-- Scalar transport is literally restriction along the inverse ring isomorphism.
Source: Stacks 03CZ (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
def transport {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) : Modules R ⥤ Modules S :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map a.inv)

/-- Additivity for inverse scalar restriction.
Source: Stacks 03D7 (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
instance transportAdditive {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    (transport a).Additive := by
  unfold transport
  infer_instance

/-- Preservation of finite limits for inverse scalar restriction.
Source: Stacks 03D7 (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
instance transportLimits {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    PreservesFiniteLimits (transport a) := by
  unfold transport
  infer_instance

/-- Preservation of finite colimits for inverse scalar restriction.
Source: Stacks 03D7 (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
instance transportColimits {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    PreservesFiniteColimits (transport a) := by
  unfold transport
  infer_instance

attribute [local instance 21000] transportAdditive transportLimits transportColimits

/-- The canonical derived comparison for an exact commuting square.
Source: Stacks 015F (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
def derivedSquare {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (rho : restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) ⋙
        transport e ≅ transport e' ⋙
          restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)) :
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).mapDerivedCategory ⋙
        (transport e).mapDerivedCategory ≅
      (transport e').mapDerivedCategory ⋙
        (restrictScalars
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso rho ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Abstract comparison data with its specified normalization predicate.
Source: Stacks 03D7, 015F and 06YY
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
structure ScalarComparisonData
    (X0 : Sort*)
    (X1 : Sort*)
    (X2 : Sort*)
    (P : ∀ (restriction : X0) (ordinary : X1) (derived : X2), Prop) where
  restriction : X0
  ordinary : X1
  derived : X2
  conditions : P restriction ordinary derived

/-- Abstract comparison data with its specified normalization predicate.
Source: Stacks 03D7, 015F and 06YY
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
structure ReductionComparisonData
    (X0 : Sort*)
    (X1 : ∀ (ordinary : X0), Sort*)
    (X2 : ∀ (ordinary : X0), Sort*)
    (X3 : Sort*)
    (X4 : ∀ (ordinary : X0) (additive : X1 ordinary) (derived : X3), Sort*)
    (X5 : ∀ (derived : X3), Sort*)
    (P : ∀ (ordinary : X0) (additive : X1 ordinary) (evaluation : X2 ordinary)
      (derived : X3) (counit : X4 ordinary additive derived)
      (derivedEvaluation : X5 derived), Prop) where
  ordinary : X0
  additive : X1 ordinary
  evaluation : X2 ordinary
  derived : X3
  counit : X4 ordinary additive derived
  derivedEvaluation : X5 derived
  conditions : P ordinary additive evaluation derived counit derivedEvaluation

/-- The actual strict reduction, with its sheafified pure tensors, all horizontal
maps and the universal derived reduction into the ordinary derived system category.
Source: Stacks 03EK, 06YY; sequence-site refinement of def-pur-section-invariant
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
def ReductionConditions (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J))
    (ordinary : Modules c.pt ⥤ StrictRingSystem B)
    [additive : ordinary.Additive]
    (evaluation : ∀ n : ℕ, ordinary ⋙ systemEvaluation B n ≅ (A (c.π.app (op n))).model.E)
    (derived : DerivedCategory (Modules c.pt) ⥤ DerivedCategory (StrictRingSystem B))
    (counit : DerivedCategory.Q ⋙ derived ⟶
    ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (derivedEvaluation : ∀ n : ℕ,
    derived ⋙ derivedSystemEvaluation B n ≅ (A (c.π.app (op n))).model.T) : Prop :=
  (∀ (M : Modules c.pt) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
      (r : (B.obj (op n)).obj.obj U) (x : M.val.obj U),
      ((evaluation m).hom.app M).val.app U
        (((ordinary.obj M).transition h).val.app U
          (((evaluation n).inv.app M).val.app U
            (systemModelTmul (A (c.π.app (op n))).model M U r x))) =
        systemModelTmul (A (c.π.app (op m))).model M U
          ((B.map (homOfLE h).op).hom.app U r) x) ∧
    (derived.IsLeftDerivedFunctor counit (HomologicalComplex.quasiIso _ (.up ℤ))) ∧
    (Functor.HasPointwiseLeftDerivedFunctor
      (ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        (HomologicalComplex.quasiIso _ (.up ℤ))) ∧
    (∀ (P : CochainComplex (Modules c.pt) ℤ),
      P.IsKFlatIndependentCoefficients → (∀ i : ℤ, IsFlatOnSite (R := c.pt) (P.X i)) →
        IsIso (counit.app P)) ∧
    (∀ (n : ℕ) (P : CochainComplex (Modules c.pt) ℤ),
      (derivedEvaluation n).hom.app (DerivedCategory.Q.obj P) ≫
          (A (c.π.app (op n))).model.ε.app P =
        (derivedSystemEvaluation B n).map (counit.app P) ≫
          (systemEvaluation B n).mapDerivedCategoryFactors.hom.app
            ((ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (evaluation n) (.up ℤ)).hom.app P))

/-- The actual strict reduction, with its sheafified pure tensors, all horizontal
maps and the universal derived reduction into the ordinary derived system category.
Source: Stacks 03EK, 06YY; sequence-site refinement of def-pur-section-invariant
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
abbrev Reduction (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) :=
  ReductionComparisonData
    (Modules c.pt ⥤ StrictRingSystem B)
    (fun ordinary ↦
      ordinary.Additive)
    (fun ordinary ↦
      ∀ n : ℕ, ordinary ⋙ systemEvaluation B n ≅ (A (c.π.app (op n))).model.E)
    (DerivedCategory (Modules c.pt) ⥤ DerivedCategory (StrictRingSystem B))
    (fun ordinary additive derived ↦
      letI := additive; DerivedCategory.Q ⋙ derived ⟶
    ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (fun derived ↦
      ∀ n : ℕ,
    derived ⋙ derivedSystemEvaluation B n ≅ (A (c.π.app (op n))).model.T)
    (fun ordinary additive evaluation derived counit derivedEvaluation ↦
      ReductionConditions B c A (additive := additive) ordinary evaluation derived counit
        derivedEvaluation)

/-- The reduction's recorded additive structure.
Source: Stacks 03EK (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
instance Reduction.additive (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (D : Reduction B c A) : D.ordinary.Additive :=
  ReductionComparisonData.additive D

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard derivedSquare systemModelTmul
  Functor.mapDerivedCategoryNatIso
  DerivedCategory.Q DerivedCategory.Qh DerivedCategory.quotientCompQhIso

private def scalarRestrictionSquare {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom) :
    restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) ⋙
        transport e ≅ transport e' ⋙
          restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b) := by
  have h' : e.inv ≫ a = b ≫ e'.inv := by
    apply (cancel_epi e.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [h]
    simp
  exact systemScalarRestrictionComposition e.inv a (e.inv ≫ a) rfl ≪≫
    (systemScalarRestrictionComposition b e'.inv (e.inv ≫ a) h').symm

private def transportInverse {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    transport a ⋙ transport a.symm ≅ 𝟭 (Modules R) :=
  systemScalarRestrictionComposition a.hom a.inv (𝟙 R) (by simp) ≪≫
    systemScalarRestrictionUnit (𝟙 R) rfl


private def scalarTransportEquivalence {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    Modules R ≌ Modules S where
  functor := transport a
  inverse := transport a.symm
  unitIso := (transportInverse a).symm
  counitIso := transportInverse a.symm
  functor_unitIso_comp := by
    intro M
    ext U x
    rfl

private theorem normalizedComparison_exists
    {A₀ B₀ C₀ D₀ : Type*} [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    {L : A₀ ⥤ B₀} {U : B₀ ⥤ A₀} {L' : C₀ ⥤ D₀} {U' : D₀ ⥤ C₀}
    (a : L ⊣ U) (b : L' ⊣ U') (G : A₀ ⥤ C₀) (H : B₀ ⥤ D₀)
    [G.IsEquivalence] [H.IsEquivalence] (ρ : U ⋙ G ≅ H ⋙ U') :
    ∃! j : L ⋙ H ≅ G ⋙ L', (mateEquiv a b j.inv).natTrans = ρ.hom := by
  obtain ⟨j, hj, hu, _⟩ := exists_equivalenceAdjunctionComparison
    G.asEquivalence H.asEquivalence a b ρ
  exact ⟨j, hj, hu⟩

private def normalizedComparison
    {A₀ B₀ C₀ D₀ : Type*} [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    {L : A₀ ⥤ B₀} {U : B₀ ⥤ A₀} {L' : C₀ ⥤ D₀} {U' : D₀ ⥤ C₀}
    (a : L ⊣ U) (b : L' ⊣ U') (G : A₀ ⥤ C₀) (H : B₀ ⥤ D₀)
    [G.IsEquivalence] [H.IsEquivalence] (ρ : U ⋙ G ≅ H ⋙ U') :
    L ⋙ H ≅ G ⋙ L' :=
  (normalizedComparison_exists a b G H ρ).exists.choose

private instance transportIsEquivalence {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    (transport a).IsEquivalence := (scalarTransportEquivalence a).isEquivalence_functor

private def ordinaryScalarSquare {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b) :
    A.model.E ⋙ transport e' ≅ transport e ⋙ B.model.E :=
  normalizedComparison A.ordinaryAdj B.ordinaryAdj (transport e)
    (transport e') (scalarRestrictionSquare a b e e' h)

attribute [local irreducible] ordinaryScalarSquare

private def derivedScalarSquare {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b) :
    A.model.T ⋙ (transport e').mapDerivedCategory ≅
      (transport e).mapDerivedCategory ⋙ B.model.T :=
  normalizedComparison A.adjunction B.adjunction (transport e).mapDerivedCategory
    (transport e').mapDerivedCategory (derivedSquare a b e e' (scalarRestrictionSquare a b e e' h))

attribute [local irreducible] derivedScalarSquare

private def reductionTransition (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (M : Modules c.pt) {m n : ℕ} (h : m ≤ n) :
    (A (c.π.app (op n))).model.E.obj M ⟶
      (systemRestriction B h).obj ((A (c.π.app (op m))).model.E.obj M) :=
  (A (B.map (homOfLE h).op)).ordinaryAdj.homEquiv _ _
    ((systemScalarModelComposition (c.w (homOfLE h).op).symm
      (A (c.π.app (op n))) (A (B.map (homOfLE h).op))
      (A (c.π.app (op m)))).hom.app M)

private theorem reductionTransition_tmul
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (M : Modules c.pt) {m n : ℕ} (h : m ≤ n)
    (U : Cᵒᵖ) (r : (B.obj (op n)).obj.obj U) (x : M.val.obj U) :
    (reductionTransition B c A M h).val.app U
        (systemModelTmul (A (c.π.app (op n))).model M U r x) =
      systemModelTmul (A (c.π.app (op m))).model M U
        ((B.map (homOfLE h).op).hom.app U r) x := by
  dsimp only [reductionTransition]
  rw [Adjunction.homEquiv_unit]
  change ((systemScalarModelComposition (c.w (homOfLE h).op).symm
      (A (c.π.app (op n))) (A (B.map (homOfLE h).op))
      (A (c.π.app (op m)))).hom.app M).val.app U
    (((A (B.map (homOfLE h).op)).ordinaryAdj.unit.app
      ((A (c.π.app (op n))).model.E.obj M)).val.app U _) = _
  rw [(A (B.map (homOfLE h).op)).unit_normalized]
  rw [systemScalarModelComposition_tmul]
  simp only [one_mul]

private def reductionObj (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (M : Modules c.pt) : StrictRingSystem B where
  level n := (A (c.π.app (op n))).model.E.obj M
  transition := reductionTransition B c A M
  identity := by
    intro n U x
    let η := systemScalarRestrictionUnit (B.map (homOfLE (Nat.le_refl n)).op)
      (B.map_id (op n))
    have he : reductionTransition B c A M (Nat.le_refl n) =
        η.inv.app ((A (c.π.app (op n))).model.E.obj M) := by
      apply systemScalarModel_hom_ext (A (c.π.app (op n)))
      intro V y
      change (reductionTransition B c A M (Nat.le_refl n)).val.app V _ =
        systemModelTmul (A (c.π.app (op n))).model M V 1 y
      simpa only [map_one] using
        reductionTransition_tmul B c A M (Nat.le_refl n) V 1 y
    exact congrArg (fun f ↦ f.val.app U x) he
  compose := by
    intro l m n h k U x
    have hc : B.map (homOfLE (h.trans k)).op =
        B.map (homOfLE k).op ≫ B.map (homOfLE h).op := by
      rw [← B.map_comp]
      rfl
    let η := systemScalarRestrictionComposition _ _ _ hc
    have he : reductionTransition B c A M (h.trans k) =
        reductionTransition B c A M k ≫
          (systemRestriction B k).map (reductionTransition B c A M h) ≫
          η.hom.app ((A (c.π.app (op l))).model.E.obj M) := by
      apply systemScalarModel_hom_ext (A (c.π.app (op n)))
      intro V y
      change (reductionTransition B c A M (h.trans k)).val.app V _ =
        (reductionTransition B c A M h).val.app V
          ((reductionTransition B c A M k).val.app V _)
      rw [reductionTransition_tmul, reductionTransition_tmul]
      simp only [map_one]
      rw [reductionTransition_tmul]
      simp only [map_one]
      rfl
    exact congrArg (fun f ↦ f.val.app U x) he

private def reductionMap (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) {M N : Modules c.pt} (f : M ⟶ N) :
    reductionObj B c A M ⟶ reductionObj B c A N where
  app n := (A (c.π.app (op n))).model.E.map f
  comm := by
    intro m n h
    apply systemScalarModel_hom_ext (A (c.π.app (op n)))
    intro U x
    change (reductionTransition B c A N h).val.app U
        (((A (c.π.app (op n))).model.E.map f).val.app U _) =
      ((A (c.π.app (op m))).model.E.map f).val.app U
        ((reductionTransition B c A M h).val.app U _)
    rw [systemScalarModel_map_tmul, reductionTransition_tmul,
      reductionTransition_tmul, systemScalarModel_map_tmul]

private def reductionFunctor (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) : Modules c.pt ⥤ StrictRingSystem B where
  obj := reductionObj B c A
  map := reductionMap B c A
  map_id M := by
    apply strictRingSystem_hom_ext
    intro n
    exact (A (c.π.app (op n))).model.E.map_id M
  map_comp f g := by
    apply strictRingSystem_hom_ext
    intro n
    exact (A (c.π.app (op n))).model.E.map_comp f g

private instance reductionFunctorAdditive
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) : (reductionFunctor B c A).Additive where
  map_add := by
    intro M N f g
    apply strictRingSystem_hom_ext
    intro n
    change (A (c.π.app (op n))).model.E.map (f + g) = _
    rw [Functor.map_add]
    exact ((systemEvaluation B n).map_add
      (f := (reductionFunctor B c A).map f) (g := (reductionFunctor B c A).map g)).symm

attribute [local irreducible] reductionFunctor

private structure DerivedReductionPackage
    (T : Sort*) (E : T → Sort*) (V : T → Sort*)
    (P : ∀ t, E t → V t → Prop) where
  derived : T
  counit : E derived
  derivedEvaluation : V derived
  conditions : P derived counit derivedEvaluation

end SheafOfModules.QuotientIsoTransport
