/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientScalarCochainEvaluation
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionOrdinaryQuotientIso
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionAssociationSuccessor
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionFiniteAssociation
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionOrdinaryAssociationChain
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionRestrictedTower
import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationScalarUnits
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationQuotientUnits
import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationTensorCoordinates
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-! # Scalar extension of ordinary quotient presentations

Source: Stacks 03EK, 03D7, 06YY and 07A4. The completed-ring tensor association,
its quotient successors, and its unit formula are proved before applying pullback.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
section OrdinaryQuotientScalarSectionCasts

set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction scalarReductionExtension coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted constantSheaf
attribute [local implicit_reducible] integralCoefficientCommRingSheaf
  SemilinearSections.systemRing
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  Functor.mapHomologicalComplex HomologicalComplex.complexOfFunctorsToFunctorToComplex

private theorem evaluation_section_heq {X : Scheme.{t}}
    (N : coefficientSequenceModules l E X) (n : ℕ) (U : X.ProEtᵒᵖ)
    (x : N.val.obj (op (n, U.unop))) :
    HEq (coefficientEvaluationSection l E X N n U x) x := by rfl

private theorem evaluation_map_section {X : Scheme.{t}}
    {N N' : coefficientSequenceModules l E X} (g : N ⟶ N')
    (n : ℕ) (U : X.ProEtᵒᵖ) (x : N.val.obj (op (n, U.unop))) :
    (((coefficientSequenceEvaluation l E X n).map g).val.app U)
      (coefficientEvaluationSection l E X N n U x) =
    coefficientEvaluationSection l E X N' n U
      (g.val.app (op (n, U.unop)) x) := rfl

private theorem eqToHom_section {C : Type v} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {N N' : SheafOfModules.{u} R} (h : N = N') (U : Cᵒᵖ) (x : N.val.obj U) :
    HEq ((eqToHom h).val.app U x) x := by
  subst N'
  rfl

private theorem restrictionEvaluation_section {X : Scheme.{t}}
    (N : coefficientSequenceModules l E X) (n : ℕ) (U : X.ProEtᵒᵖ)
    (x : N.val.obj (op (n, U.unop))) :
    (((eqToIso (coefficientSequenceRestriction_evaluation l E X n)).app N).hom.val.app U)
      (integralComparisonRestrictedSection l E X N n U x) =
        coefficientEvaluationSection l E X N n U x := by
  simp only [Iso.app_hom, eqToIso.hom, eqToHom_app]
  apply eq_of_heq
  have h := eqToHom_section
    (congrArg (fun F ↦ F.obj N) (coefficientSequenceRestriction_evaluation l E X n))
    U (integralComparisonRestrictedSection l E X N n U x)
  have hc : HEq (integralComparisonRestrictedSection l E X N n U x) x :=
    cast_heq (integralComparisonRestrictedSectionType l E X N n U).symm x
  exact (h.trans hc).trans (evaluation_section_heq l E N n U x).symm

private theorem cast_map {A A' B B' : Type v} (hA : A = A') (hB : B = B')
    (f : A → B) (g : A' → B') (h : HEq f g) (x : A') :
    f (cast hA.symm x) = cast hB.symm (g x) := by
  cases hA
  cases hB
  exact congrFun (eq_of_heq h) x

private theorem restriction_map_section {X : Scheme.{t}}
    {N N' : coefficientSequenceModules l E X} (g : N ⟶ N')
    (n : ℕ) (U : X.ProEtᵒᵖ) (x : N.val.obj (op (n, U.unop))) :
    ((((coefficientSequenceRestriction l E X).map g).app (op n)).val.app U)
      (integralComparisonRestrictedSection l E X N n U x) =
    integralComparisonRestrictedSection l E X N' n U
      (g.val.app (op (n, U.unop)) x) := by
  have h : HEq (fun y ↦
      ((((coefficientSequenceRestriction l E X).map g).app (op n)).val.app U) y)
      (fun y : N.val.obj (op (n, U.unop)) ↦ g.val.app (op (n, U.unop)) y) := by
    unfold coefficientSequenceRestriction
    exact (coefficientSequenceRestriction_exists l E X).exists.choose_spec.2.2 g n U
  exact cast_map (integralComparisonRestrictedSectionType l E X N n U)
    (integralComparisonRestrictedSectionType l E X N' n U) _ _ h x

private theorem eqToHom_ab_heq {A B : AddCommGrpCat.{v}} (h : A = B) (x : A) :
    HEq ((eqToHom h) x) x := by
  subst B
  rfl

private theorem sequenceSection_heq (N : coefficientSequenceModules l E W)
    (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj N).val.obj U) :
    HEq (integralComparisonSequenceSection l E W N n U x) x :=
  eqToHom_ab_heq (coefficientSequenceEvaluationAb_eq l E W N n U) x


end OrdinaryScalarTowerProof
end WeilConjectures

end OrdinaryQuotientScalarSectionCasts

section OrdinaryQuotientScalarSections

set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction scalarReductionExtension coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted constantSheaf
attribute [local implicit_reducible] integralCoefficientCommRingSheaf
  SemilinearSections.systemRing
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  Functor.mapHomologicalComplex HomologicalComplex.complexOfFunctorsToFunctorToComplex

private theorem finiteUnit_eq (K : scalarReductionSource l E W)
    (n : ℕ) (U : W.ProEtᵒᵖ) (x : K.val.obj U) :
    CoefficientExtensionAssociation.finiteUnitSection l E W K n U x =
      unrestrictedIntegralTensorSection l E W n K U 1 x := by
  unfold CoefficientExtensionAssociation.finiteUnitSection
    CoefficientExtensionAssociation.normalizedUnitSection
    CoefficientExtensionAssociation.quotientAdjunction
  exact (scalarReductionExtension_adjunction l E W n).choose_spec K U x

/-- The presentation inverse takes the kappa-inverse unit section to M's quotient unit.
Source: Stacks 03D7, naturality and normalization of the ordinary quotient unit.
(blueprint: lem-trf-ordinary-quotient-scalar-presentation-unit).
Proof: invert the presentation comparison equation, evaluate at degree i and
apply it to 1 tensor x. Evaluation commutes with the presentation inverse, and
its section casts are HEq to identity. The normalized quotient-adjunction unit
identifies the finite unit section with 1 tensor x, giving the stated formula. -/
private theorem presentationUnit
    (M : CompletionUnit.OrdinaryModel l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (a : (M.quotient l E W).obj P ≅ C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj P)
    (hκ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
        κ n = (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P)
    (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ) (x : (P.X i).val.obj U) :
    (a.inv.f i).val.app (op (n, U.unop))
      (integralComparisonSequenceSection l E W (C.X i) n U
        (((κ n).inv.f i).val.app U
          (unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x))) =
      CoefficientExtensionAssociation.quotientUnitSection l E W M (P.X i) n U x := by
  let z := unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x
  let w := integralComparisonSequenceSection l E W (C.X i) n U
    (((κ n).inv.f i).val.app U z)
  have hi := congrArg (fun b ↦ b.inv.f i) (hκ n)
  simp only [Iso.trans_inv, HomologicalComplex.comp_f, Functor.mapIso_inv,
    Functor.mapHomologicalComplex_map_f] at hi
  have hx := congrArg (fun b ↦ b.val.app U z) hi
  have hw : coefficientEvaluationSection l E W (C.X i) n U w =
      ((κ n).inv.f i).val.app U z :=
    eq_of_heq ((evaluation_section_heq l E (C.X i) n U w).trans
      (sequenceSection_heq l E W (C.X i) n U _))
  have hm := evaluation_map_section l E (a.inv.f i) n U w
  rw [hw] at hm
  change ((coefficientSequenceEvaluation l E W n).map (a.inv.f i)).val.app U
      (((κ n).inv.f i).val.app U z) =
    ((M.evaluation n).inv.app (P.X i)).val.app U z at hx
  rw [hx] at hm
  have he := evaluation_section_heq l E (M.tensor.obj (P.X i)) n U
    ((a.inv.f i).val.app (op (n, U.unop)) w)
  unfold CoefficientExtensionAssociation.quotientUnitSection
  rw [finiteUnit_eq l E W]
  exact eq_of_heq (he.symm.trans (heq_of_eq hm.symm))

end OrdinaryScalarTowerProof
end WeilConjectures

end OrdinaryQuotientScalarSections

section OrdinaryQuotientScalarTowerLevels

set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction constantSheaf
  completedIntegralCommRingProjectionUnrestricted
attribute [local implicit_reducible] integralCoefficientCommRingSheaf

private def finiteComparison
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (n : ℕ) :
    M.tensor ⋙ A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      integralScalarReduction l E L ι W n :=
  Functor.isoWhiskerLeft M.tensor (ρ n) ≪≫
    Functor.isoWhiskerRight (C := scalarReductionSource l E W)
      (D := normalizedDVRModules l E W n) (E := normalizedDVRModules l L W n)
      (M.evaluation n) (A.levels n).model.E ≪≫ association n

private def direct (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W) :
    CochainComplex (scalarReductionSource l E W) ℤ ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ :=
  M.quotient l E W ⋙ A.scalar.model.E.mapHomologicalComplex (.up ℤ)

private def directEvaluation
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (n : ℕ) :
    direct l E L ι W A M ⋙
      (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        integralScalarFiniteComplex l E L ι W n :=
  NatIso.ofComponents (fun P ↦ HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (finiteComparison l E L ι W A M ρ association n).app (P.X i)) (by
      intro i j hij
      exact ((finiteComparison l E L ι W A M ρ association n).hom.naturality
        (P.d i j)).symm)) (by
    intro P Q f
    apply HomologicalComplex.hom_ext
    intro i
    exact (finiteComparison l E L ι W A M ρ association n).hom.naturality (f.f i))

private theorem directEvaluation_hom_f
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) (i : ℤ) :
    ((directEvaluation l E L ι W A M ρ association n).hom.app P).f i =
      (finiteComparison l E L ι W A M ρ association n).hom.app (P.X i) := rfl

private theorem directTransition
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) (i : ℤ)
    (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l L W (n + 1)).obj
      (((direct l E L ι W A M).obj P).X i)).val.obj U) :
    HEq (((coefficientSequenceTransition l L W (Nat.le_succ n)).app
      (((direct l E L ι W A M).obj P).X i)).val.app U x)
      ((((directEvaluation l E L ι W A M ρ association n).inv.app P).f i).val.app U
        ((((integralScalarTransition l E L ι W n).app P).f i).val.app U
          ((((directEvaluation l E L ι W A M ρ association (n + 1)).hom.app P).f i).val.app U
            x))) := by
  exact coefficientExtensionAssociation_successor l E L ι W A M ρ hρ
    association hassociation P n i U x

attribute [local irreducible] SemilinearSections.systemMap
  CategoryTheory.Functor.leftAdjoint HasDerivedCategory.standard
attribute [local implicit_reducible] SemilinearSections.systemRing
  coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf

private theorem coefficientEvaluation_smul
    (N : coefficientSequenceModules l L W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L W n).obj.obj U)
    (x : N.val.obj (op (n, U.unop))) :
    s • (show ((coefficientSequenceEvaluation l L W n).obj N).val.obj U from x) =
      (s • x : N.val.obj (op (n, U.unop))) := by
  change ((eqToHom (coefficientSequenceEvaluationRing_eq l L W n).symm).hom.app U).hom s • x = _
  rw [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

private theorem evaluatedUnit_raw_eq
    (A : CoefficientExtensionSystems l E L ι W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (N : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj N).val.obj U) :
    CoefficientExtensionAssociation.evaluatedUnitSection l E L ι W A ρ N n U x =
      (show ((coefficientSequenceEvaluation l L W n).obj
        (A.scalar.model.E.obj N)).val.obj U from
          (A.scalar.ordinaryAdjunction.unit.app N).val.app (op (n, U.unop)) x) := by
  exact eq_of_heq (CoefficientExtensionAssociation.evaluatedUnitSection_raw
    l E L ι W A ρ hρ N n U x)

private theorem evaluatedUnit_smul_raw
    (A : CoefficientExtensionSystems l E L ι W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (N : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (s : (coefficientSequenceCommRingSheaf l L W).obj.obj (op (n, U.unop)))
    (x : ((coefficientSequenceEvaluation l E W n).obj N).val.obj U) :
    HEq
      (s • (show (A.scalar.model.E.obj N).val.obj (op (n, U.unop)) from
        (A.scalar.ordinaryAdjunction.unit.app N).val.app (op (n, U.unop)) x))
      (s • CoefficientExtensionAssociation.evaluatedUnitSection l E L ι W A ρ N n U x) := by
  have hr' := evaluatedUnit_raw_eq l E L ι W A ρ hρ N n U x
  have hs := coefficientEvaluation_smul l L W (A.scalar.model.E.obj N) n U s
    (show (A.scalar.model.E.obj N).val.obj (op (n, U.unop)) from
      (A.scalar.ordinaryAdjunction.unit.app N).val.app (op (n, U.unop)) x)
  have hm := congrArg (fun z :
    ((coefficientSequenceEvaluation l L W n).obj (A.scalar.model.E.obj N)).val.obj U ↦
      s • z) hr'.symm
  have hh := hs.symm.trans hm
  exact heq_of_eq hh

end OrdinaryScalarTowerProof
end WeilConjectures

end OrdinaryQuotientScalarTowerLevels

section OrdinaryQuotientScalarTowerConstruction

set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction constantSheaf
  completedIntegralCommRingProjectionUnrestricted
attribute [local implicit_reducible] integralCoefficientCommRingSheaf

attribute [local irreducible] direct directEvaluation finiteComparison

/-- Assemble the explicit finite balanced comparisons into an all-complex tower.
Source: Stacks 03D7, 03EK, and successor compatibility on the sequence site.
(blueprint: lem-trf-ordinary-quotient-scalar-tower-construction).
Proof: restriction-evaluation followed by the finite comparison defines each level.
The given successor identity proves their naturality along adjacent arrows; the
opposite-sequence construction extends this to all arrows. Pointwise inverses
and naturality in the complex give the natural isomorphism and component formula. -/
private theorem comparison_exists
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association)
    :
    let direct := direct l E L ι W A M
    let directEvaluation := directEvaluation l E L ι W A M ρ association
    ∃ e : direct ⋙ (coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
      integralScalarTowerFunctor l E L ι W,
      ∀ (P : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ),
        (e.hom.app P).app (op n) =
          (coefficientRestrictedComplexEvaluation l L W n).hom.app (direct.obj P) ≫
            ((scalarReductionRestriction l L W n).mapHomologicalComplex (.up ℤ)).map
              ((directEvaluation n).hom.app P) := by
  classical
  let direct := direct l E L ι W A M
  let directEvaluation := directEvaluation l E L ι W A M ρ association
  have htransition := directTransition l E L ι W A M ρ hρ association hassociation
  let H := direct ⋙ (coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)
  let a (n : ℕ) : H ⋙
      ((evaluation ℕᵒᵖ (scalarReductionSource l L W)).obj (op n)).mapHomologicalComplex
        (.up ℤ) ≅ integralScalarLevel l E L ι W n :=
    Functor.isoWhiskerLeft direct (coefficientRestrictedComplexEvaluation l L W n) ≪≫
      Functor.isoWhiskerRight (directEvaluation n)
        ((scalarReductionRestriction l L W n).mapHomologicalComplex (.up ℤ))
  have ha (P : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) :
      (H.obj P).asFunctor.map (homOfLE (Nat.le_succ n)).op ≫ (a n).hom.app P =
        (a (n + 1)).hom.app P ≫ (integralScalarTransition l E L ι W n).app P := by
    apply (cancel_mono ((a n).inv.app P)).1
    simp only [Category.assoc, Iso.hom_inv_id_app]
    apply HomologicalComplex.hom_ext
    intro i
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext x
    have hobj (k : ℕ) := congrArg (fun F ↦ F.obj ((direct.obj P).X i))
      (coefficientSequenceRestriction_evaluation l L W k)
    have hs (k : ℕ) :
        ((scalarReductionRestriction l L W k).obj
          ((coefficientSequenceEvaluation l L W k).obj ((direct.obj P).X i))).val.presheaf.obj V =
          ((coefficientSequenceEvaluation l L W k).obj ((direct.obj P).X i)).val.presheaf.obj V :=
      restrictScalars_presheaf_obj _ _ _
    let y : ((coefficientSequenceEvaluation l L W (n + 1)).obj
        ((direct.obj P).X i)).val.obj V :=
      cast (congrArg (fun G : AddCommGrpCat ↦ ↥G)
        ((congrArg (fun M : scalarReductionSource l L W ↦ M.val.presheaf.obj V)
          (hobj (n + 1))).trans (hs (n + 1)))) x
    have hy : HEq y x := by
      exact cast_heq _ x
    have hh := restriction_transition_apply_heq l L W ((direct.obj P).X i)
      (Nat.le_succ n) V x y hy.symm
    have ht := htransition P n i V y
    simp only [a, Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
      HomologicalComplex.comp_f, HomologicalComplex.id_f,
      Functor.mapHomologicalComplex_map_f,
      restrictedEvaluation_hom_f, restrictedEvaluation_inv_f]
    erw [Category.comp_id]
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    apply eq_of_heq
    refine (hh.trans ht).trans ?_
    have hc0 := module_eqToHom_apply_heq l L W (hobj (n + 1)) V x
    have hc1 := restrictionMap_apply_heq l L W (n + 1)
      (((directEvaluation (n + 1)).hom.app P).f i) V _ y (hc0.trans hy.symm)
    have hc2 := hcongr_apply rfl
      (HEq.rfl (a := fun x ↦
        ((((integralScalarTransition l E L ι W n).app P).f i).val.app V) x)) hc1
    have hc3 := restrictionMap_apply_heq l L W n
      (((directEvaluation n).inv.app P).f i) V _ _ hc2
    have hc4 := module_eqToHom_apply_heq l L W (hobj n).symm V
      (((((scalarReductionRestriction l L W n).map
        (((directEvaluation n).inv.app P).f i)).val.app V))
          (((((integralScalarTransition l E L ι W n).app P).f i).val.app V)
            (((((scalarReductionRestriction l L W (n + 1)).map
              (((directEvaluation (n + 1)).hom.app P).f i)).val.app V))
                (((eqToHom (hobj (n + 1))).val.app V) x))))
    exact (hc4.trans hc3).symm
  let T := integralScalarTowerFunctor l E L ι W
  obtain ⟨e, he⟩ := assembleTowerIso H T a (fun P n ↦ by
    dsimp only [T, Functor.comp_obj, integralScalarTowerFunctor]
    erw [Functor.flip_obj_map, Functor.ofOpSequence_map_homOfLE_succ]
    exact ha P n)
  refine ⟨e, ?_⟩
  intro P n
  rw [he]
  simp only [a, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rfl

end OrdinaryScalarTowerProof
end WeilConjectures

end OrdinaryQuotientScalarTowerConstruction

section OrdinaryQuotientScalarNormalization

set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction scalarReductionExtension coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted constantSheaf
  SemilinearSections.systemMap CategoryTheory.Functor.leftAdjoint HasDerivedCategory.standard
attribute [local implicit_reducible] direct integralCoefficientCommRingSheaf
  SemilinearSections.systemRing
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  Functor.mapHomologicalComplex HomologicalComplex.complexOfFunctorsToFunctorToComplex

/-- The finite balanced comparison takes scalar multiples of quotient units to tensors.
Source: Stacks 03D7 and 03EK, the normalized balanced associator.
(blueprint: lem-trf-ordinary-quotient-scalar-tensor-normalization).
Proof: apply the forward comparison to its proved inverse-coordinate tensor
formula and cancel the inverse isomorphism. This calculation holds for every
completed module, scalar and section, with no flatness condition. -/
private theorem finiteComparison_unit
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
    coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (association : ∀ n : ℕ,
    scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association)
    (K : scalarReductionSource l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L W n).obj.obj U) (x : K.val.obj U) :
    ((finiteComparison l E L ι W A M ρ association n).hom.app K).val.app U
      (s • CoefficientExtensionAssociation.evaluatedUnitSection l E L ι W A ρ
        (M.tensor.obj K) n U
          (CoefficientExtensionAssociation.quotientUnitSection l E W M K n U x)) =
      integralScalarTensorSection l E L ι W n K U s x := by
  have h := CoefficientExtensionAssociation.association_inverse_tensor l E L ι W A M ρ
    association hassociation K n U s x
  exact (congrArg
    (fun y ↦ ((finiteComparison l E L ι W A M ρ association n).hom.app K).val.app U y)
    h.symm).trans
      (congrArg (fun f ↦ f.val.app U (integralScalarTensorSection l E L ι W n K U s x))
        ((finiteComparison l E L ι W A M ρ association n).app K).inv_hom_id)

private theorem comparison_section
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (e : ((direct l E L ι W A M) ⋙
        (coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex).obj P ≅
      (integralScalarTowerFunctor l E L ι W).obj P)
    (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
    (he : e.hom.app (op n) =
      (coefficientRestrictedComplexEvaluation l L W n).hom.app
        ((direct l E L ι W A M).obj P) ≫
      ((scalarReductionRestriction l L W n).mapHomologicalComplex (.up ℤ)).map
        ((directEvaluation l E L ι W A M ρ association n).hom.app P))
    (y : (A.scalar.model.E.obj (M.tensor.obj (P.X i))).val.obj (op (n, U.unop)))
    (z : ((coefficientSequenceEvaluation l L W n).obj
      (A.scalar.model.E.obj (M.tensor.obj (P.X i)))).val.obj U)
    (hy : HEq y z) :
    ((e.hom.app (op n)).f i).val.app U
      (integralComparisonRestrictedSection l L W
        (A.scalar.model.E.obj (M.tensor.obj (P.X i))) n U y) =
      ((finiteComparison l E L ι W A M ρ association n).hom.app (P.X i)).val.app U z := by
  rw [he]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    restrictedEvaluation_hom_f, directEvaluation_hom_f,
    SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  have ht : HEq
      ((((eqToIso (coefficientSequenceRestriction_evaluation l L W n)).app
        (A.scalar.model.E.obj (M.tensor.obj (P.X i))))).hom.val.app U
          (integralComparisonRestrictedSection l L W
            (A.scalar.model.E.obj (M.tensor.obj (P.X i))) n U y)) z :=
    (heq_of_eq (restrictionEvaluation_section l L
      (A.scalar.model.E.obj (M.tensor.obj (P.X i))) n U y)).trans
        ((evaluation_section_heq l L
          (A.scalar.model.E.obj (M.tensor.obj (P.X i))) n U y).trans hy)
  simp only [Iso.app_hom, eqToIso.hom, eqToHom_app] at ht
  exact eq_of_heq (restrictionMap_apply_heq l L W n
    ((finiteComparison l E L ι W A M ρ association n).hom.app (P.X i)) U _ z ht)

private theorem normalizedComparison
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association)
    (F : coefficientSequenceModules l E W ⥤ coefficientSequenceModules l L W)
    [F.Additive] (hF : A.scalar.model.E = F) :
    let T := F.mapHomologicalComplex (.up ℤ) ⋙
      (coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex
    ∃ θ : M.quotient l E W ⋙ T ≅ integralScalarTowerFunctor l E L ι W,
      ∀ (P : CochainComplex (scalarReductionSource l E W) ℤ)
        (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
        (a : (M.quotient l E W).obj P ≅ C)
        (κ : ∀ n : ℕ,
          ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
            (unrestrictedIntegralFiniteComplex l E W n).obj P),
        (∀ n : ℕ,
          ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
            κ n = (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P) →
        ∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
          (s : (coefficientSequenceCommRingSheaf l L W).obj.obj (op (n, U.unop)))
          (x : (P.X i).val.obj U)
          (y : (F.obj (C.X i)).val.obj (op (n, U.unop))),
          HEq y (s • (show (A.scalar.model.E.obj (C.X i)).val.obj (op (n, U.unop)) from
            (A.scalar.ordinaryAdjunction.unit.app (C.X i)).val.app (op (n, U.unop))
              (integralComparisonSequenceSection l E W (C.X i) n U
                (((κ n).inv.f i).val.app U
                  (unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x))))) →
          (((T.mapIso a.symm ≪≫ θ.app P).hom.app (op n)).f i).val.app U
            (integralComparisonRestrictedSection l L W (F.obj (C.X i)) n U y) =
            integralScalarTensorSection l E L ι W n (P.X i) U s x := by
  subst F
  dsimp only
  obtain ⟨θ, hθ⟩ := comparison_exists l E L ι W A M ρ hρ association hassociation
  refine ⟨θ, ?_⟩
  intro P C a κ hκ n i U s x y hy
  let w := integralComparisonSequenceSection l E W (C.X i) n U
    (((κ n).inv.f i).val.app U
      (unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x))
  have hp := presentationUnit l E W M P C a κ hκ n i U x
  have hn := congrArg (fun f ↦ f.val.app (op (n, U.unop)) w)
    (A.scalar.ordinaryAdjunction.unit.naturality (a.inv.f i))
  have hy' := eq_of_heq hy
  subst y
  simp only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.mapIso_hom,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [restriction_map_section l L
    (A.scalar.model.E.map (a.inv.f i)) n U]
  change (A.scalar.ordinaryAdjunction.unit.app (M.tensor.obj (P.X i))).val.app
      (op (n, U.unop)) ((a.inv.f i).val.app (op (n, U.unop)) w) =
    (A.scalar.model.E.map (a.inv.f i)).val.app (op (n, U.unop))
      ((A.scalar.ordinaryAdjunction.unit.app (C.X i)).val.app (op (n, U.unop)) w) at hn
  rw [hp] at hn
  dsimp only [w] at hn
  erw [map_smul, ← hn]
  have hu := evaluatedUnit_smul_raw l E L ι W A ρ hρ (M.tensor.obj (P.X i)) n U s
    (CoefficientExtensionAssociation.quotientUnitSection l E W M (P.X i) n U x)
  exact (comparison_section l E L ι W A M ρ association P (θ.app P) n i U
    (hθ P n) _ _ hu).trans
      (finiteComparison_unit l E L ι W A M ρ association hassociation (P.X i) n U s x)

end OrdinaryScalarTowerProof
end WeilConjectures

end OrdinaryQuotientScalarNormalization

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction scalarReductionExtension integralOrdinaryScalar
  completedIntegralCommRingProjectionUnrestricted constantSheaf HasDerivedCategory.standard
  WeilConjectures.scalarAdjunction
  unrestrictedIntegralTensorSection integralOrdinaryTensorSection integralScalarTensorSection

attribute [local implicit_reducible] integralCoefficientCommRingSheaf integralCoefficientSheaf
  unrestrictedIntegralReductionFunctor Functor.mapHomologicalComplex
  SemilinearSections.systemRing coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf

private theorem finiteReductionUnit (Y : Scheme.{u})
    (M : scalarReductionSource l L Y) (n : ℕ) (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((scalarReductionExtension_adjunction l L Y n).choose.unit.app M).val.app U x =
      unrestrictedIntegralTensorSection l L Y n M U 1 x := by
  have h := (scalarReductionExtension_adjunction l L Y n).choose_spec M U x
  dsimp only [unrestrictedIntegralTensorSection, unrestrictedIntegralReductionFunctor,
    unrestrictedIntegralReductionExistence, scalarReductionExistence] at h ⊢
  with_unfolding_all exact h

private theorem completedScalarAdj_exists (Y : Scheme.{u}) :
    ∃ a : integralOrdinaryScalar l E L ι Y ⊣
      SheafOfModules.restrictScalars ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralCompletedScalarMap l E L ι Y)),
      ∀ (M : scalarReductionSource l E Y) (U : Y.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x = integralOrdinaryTensorSection l E L ι Y M U 1 x := by
  let ho := (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (integralCompletedScalarMap l E L ι Y)).choose_spec.choose_spec
      (integralOrdinaryScalar l E L ι Y) (integralOrdinaryScalar_obj l E L ι Y)
      (fun f ↦ integralOrdinaryScalar_map l E L ι Y f)
  refine ⟨ho.choose, ?_⟩
  intro M U x
  have ht := ho.choose_spec M ((integralOrdinaryScalar l E L ι Y).obj M)
    (eqToHom (integralOrdinaryScalar_obj l E L ι Y M).symm) U x
  simp only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at ht
  unfold integralOrdinaryTensorSection
  with_unfolding_all exact ht

private def completedScalarAdj (Y : Scheme.{u}) :
    integralOrdinaryScalar l E L ι Y ⊣
      SheafOfModules.restrictScalars ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralCompletedScalarMap l E L ι Y)) :=
  (completedScalarAdj_exists l E L ι Y).choose

private theorem completedScalarAdj_unit (Y : Scheme.{u})
    (M : scalarReductionSource l E Y) (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((completedScalarAdj l E L ι Y).unit.app M).val.app U x =
      integralOrdinaryTensorSection l E L ι Y M U 1 x :=
  (completedScalarAdj_exists l E L ι Y).choose_spec M U x

attribute [local irreducible] completedScalarAdj

private def completedFiniteAssociation (Y : Scheme.{u}) (n : ℕ) :
    integralOrdinaryScalar l E L ι Y ⋙ scalarReductionExtension l L Y n ≅
      integralScalarReduction l E L ι Y n := by
  let J := Scheme.ProEt.topology Y
  let F := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  exact (WeilConjectures.associationWithUnit
    (F.map (integralCompletedScalarMap l E L ι Y))
    (F.map (completedIntegralCommRingProjectionUnrestricted l L Y n))
    (F.map (integralScalarRho l E L ι Y n))
    (by rw [← F.map_comp, integralCompletedScalarMap_projection])
    (integralOrdinaryScalar l E L ι Y) (scalarReductionExtension l L Y n)
    (integralScalarReduction l E L ι Y n)
    (completedScalarAdj l E L ι Y)
    (scalarReductionExtension_adjunction l L Y n).choose
    (WeilConjectures.scalarAdjunction l E L ι Y n)).iso

private theorem completedFiniteAssociation_unit (Y : Scheme.{u}) (n : ℕ)
    (M : scalarReductionSource l E Y) (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((completedFiniteAssociation l E L ι Y n).hom.app M).val.app U
      (unrestrictedIntegralTensorSection l L Y n
        ((integralOrdinaryScalar l E L ι Y).obj M) U 1
        (integralOrdinaryTensorSection l E L ι Y M U 1 x)) =
      integralScalarTensorSection l E L ι Y n M U 1 x := by
  let J := Scheme.ProEt.topology Y
  let F := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have h := (WeilConjectures.associationWithUnit
    (F.map (integralCompletedScalarMap l E L ι Y))
    (F.map (completedIntegralCommRingProjectionUnrestricted l L Y n))
    (F.map (integralScalarRho l E L ι Y n))
    (by rw [← F.map_comp, integralCompletedScalarMap_projection])
    (integralOrdinaryScalar l E L ι Y) (scalarReductionExtension l L Y n)
    (integralScalarReduction l E L ι Y n)
    (completedScalarAdj l E L ι Y)
    (scalarReductionExtension_adjunction l L Y n).choose
    (WeilConjectures.scalarAdjunction l E L ι Y n)).unit M U x
  change ((completedFiniteAssociation l E L ι Y n).hom.app M).val.app U
    (((scalarReductionExtension_adjunction l L Y n).choose.unit.app
      ((integralOrdinaryScalar l E L ι Y).obj M)).val.app U
        (((completedScalarAdj l E L ι Y).unit.app M).val.app U x)) =
    ((WeilConjectures.scalarAdjunction l E L ι Y n).unit.app M).val.app U x at h
  have ha := completedScalarAdj_unit l E L ι Y M U x
  have hb := finiteReductionUnit l L Y ((integralOrdinaryScalar l E L ι Y).obj M) n U
    (integralOrdinaryTensorSection l E L ι Y M U 1 x)
  have hc := WeilConjectures.scalarAdjunction_unit l E L ι Y n M U x
  have he := (congrArg (fun z ↦
    ((scalarReductionExtension_adjunction l L Y n).choose.unit.app
      ((integralOrdinaryScalar l E L ι Y).obj M)).val.app U z) ha).trans hb
  exact (congrArg (fun z ↦
    ((completedFiniteAssociation l E L ι Y n).hom.app M).val.app U z) he).symm.trans
      (h.trans hc)

attribute [local irreducible] completedFiniteAssociation

private theorem directTensor_smul (Y : Scheme.{u}) (n : ℕ)
    (M : scalarReductionSource l E Y) (U : Y.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L Y n).obj.obj U) (x : M.val.obj U) :
    integralScalarTensorSection l E L ι Y n M U s x =
      s • integralScalarTensorSection l E L ι Y n M U 1 x := by
  unfold integralScalarTensorSection
  rw [WeilConjectures.tensorSection_smul.{u + 1, u, u} (f := integralScalarRho l E L ι Y n)]
  exact (((integralScalarReductionIso l E L ι Y n).inv.app M).val.app U).hom.map_smul _ _

private def completedOrdinaryEvaluation (Y : Scheme.{u})
    (M : CompletionUnit.OrdinaryModel l L Y) (n : ℕ) :
    integralOrdinaryScalar l E L ι Y ⋙ M.tensor ⋙ coefficientSequenceEvaluation l L Y n ≅
      integralScalarReduction l E L ι Y n :=
  Functor.isoWhiskerLeft (integralOrdinaryScalar l E L ι Y) (M.evaluation n) ≪≫
    completedFiniteAssociation l E L ι Y n

private theorem completedOrdinaryEvaluation_inverse (Y : Scheme.{u})
    (M : CompletionUnit.OrdinaryModel l L Y) (n : ℕ)
    (K : scalarReductionSource l E Y) (U : Y.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L Y n).obj.obj U) (x : K.val.obj U) :
    ((completedOrdinaryEvaluation l E L ι Y M n).inv.app K).val.app U
      (integralScalarTensorSection l E L ι Y n K U s x) =
      s • CoefficientExtensionAssociation.quotientUnitSection l L Y M
        ((integralOrdinaryScalar l E L ι Y).obj K) n U
        (integralOrdinaryTensorSection l E L ι Y K U 1 x) := by
  rw [directTensor_smul, map_smul]
  congr 1
  have h := completedFiniteAssociation_unit l E L ι Y n K U x
  have hc := congrArg
    (fun z ↦ ((completedFiniteAssociation l E L ι Y n).inv.app K).val.app U z) h
  have hi := congrArg (fun z ↦ z.val.app U
    (unrestrictedIntegralTensorSection l L Y n
      ((integralOrdinaryScalar l E L ι Y).obj K) U 1
      (integralOrdinaryTensorSection l E L ι Y K U 1 x)))
    ((completedFiniteAssociation l E L ι Y n).app K).hom_inv_id
  dsimp only [completedOrdinaryEvaluation, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv]
  change ((M.evaluation n).inv.app _).val.app U
    (((completedFiniteAssociation l E L ι Y n).inv.app K).val.app U
      (integralScalarTensorSection l E L ι Y n K U 1 x)) = _
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply,
    Iso.app_hom, Iso.app_inv] at hi
  rw [← hc, hi]
  unfold CoefficientExtensionAssociation.quotientUnitSection
  rw [OrdinaryScalarTowerProof.finiteUnit_eq]

private theorem completedOrdinaryEvaluation_transition (Y : Scheme.{u})
    (M : CompletionUnit.OrdinaryModel l L Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) (i : ℤ)
    (U : Y.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l L Y (n + 1)).obj
      (M.tensor.obj ((integralOrdinaryScalar l E L ι Y).obj (P.X i)))).val.obj U) :
    HEq (((coefficientSequenceTransition l L Y (Nat.le_succ n)).app
      (M.tensor.obj ((integralOrdinaryScalar l E L ι Y).obj (P.X i)))).val.app U x)
      (((completedOrdinaryEvaluation l E L ι Y M n).inv.app (P.X i)).val.app U
        ((((integralScalarTransition l E L ι Y n).app P).f i).val.app U
          (((completedOrdinaryEvaluation l E L ι Y M (n + 1)).hom.app
            (P.X i)).val.app U x))) := by
  apply WeilConjectures.tensorTransition_of_generators l E L ι Y
    (M.tensor.obj ((integralOrdinaryScalar l E L ι Y).obj (P.X i))) P n i
    (fun k ↦ (completedOrdinaryEvaluation l E L ι Y M k).app (P.X i))
    ?_ U x
  intro V s y
  let K := (integralOrdinaryScalar l E L ι Y).obj (P.X i)
  let z := integralOrdinaryTensorSection l E L ι Y (P.X i) V 1 y
  let τ := (coefficientSequenceTransition l L Y (Nat.le_succ n)).app (M.tensor.obj K)
  let r := (integralCoefficientSheafTransition l L Y n).hom.app V s
  have hi := completedOrdinaryEvaluation_inverse l E L ι Y M (n + 1) (P.X i) V s y
  have hj := completedOrdinaryEvaluation_inverse l E L ι Y M n (P.X i) V r y
  have hs : (normalizedDVRQuotient l L Y (Nat.le_succ n)).hom.app V s = r :=
    congrArg (fun f ↦ f.hom.app V s)
      (Functor.ofOpSequence_map_homOfLE_succ (integralCoefficientSheafTransition l L Y) n)
  exact CoefficientExtensionAssociation.map_balanced_units
    (normalizedDVRQuotient l L Y (Nat.le_succ n)) τ V s r
    (((completedOrdinaryEvaluation l E L ι Y M (n + 1)).inv.app (P.X i)).val.app V
      (integralScalarTensorSection l E L ι Y (n + 1) (P.X i) V s y))
    (CoefficientExtensionAssociation.quotientUnitSection l L Y M K (n + 1) V z)
    (((completedOrdinaryEvaluation l E L ι Y M n).inv.app (P.X i)).val.app V
      (integralScalarTensorSection l E L ι Y n (P.X i) V r y))
    (CoefficientExtensionAssociation.quotientUnitSection l L Y M K n V z) hs hi hj
    (CoefficientExtensionAssociation.quotientUnitSection_transition l L Y M K n V z)

private theorem strictScalarAssociation (Y : Scheme.{u})
    (A : CoefficientExtensionSystems l E L ι Y)
    (ME : CompletionUnit.OrdinaryModel l E Y)
    (ML : CompletionUnit.OrdinaryModel l L Y)
    (ρ : ∀ n, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L Y n ≅
      coefficientSequenceEvaluation l E Y n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι Y A ρ)
    (association : ∀ n, scalarReductionExtension l E Y n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι Y n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι Y A association) :
    let := coefficientScalarModelZero A.scalar
    let F := ME.quotient l E Y ⋙ A.scalar.model.E.mapHomologicalComplex (.up ℤ)
    let G := (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ) ⋙
      ML.quotient l L Y
    let a := OrdinaryScalarTowerProof.directEvaluation l E L ι Y A ME ρ association
    let b (n : ℕ) : G ⋙
        (coefficientSequenceEvaluation l L Y n).mapHomologicalComplex (.up ℤ) ≅
        integralScalarFiniteComplex l E L ι Y n :=
      NatIso.ofComponents (fun P ↦ HomologicalComplex.Hom.isoOfComponents
        (fun i ↦ (completedOrdinaryEvaluation l E L ι Y ML n).app (P.X i))
        (by intro i j _hij; exact
          ((completedOrdinaryEvaluation l E L ι Y ML n).hom.naturality (P.d i j)).symm))
        (by intro P Q f; apply HomologicalComplex.hom_ext; intro i
            exact (completedOrdinaryEvaluation l E L ι Y ML n).hom.naturality (f.f i))
    ∃ β : F ≅ G, ∀ P n,
      ((coefficientSequenceEvaluation l L Y n).mapHomologicalComplex (.up ℤ)).map
        (β.hom.app P) = (a n).hom.app P ≫ (b n).inv.app P := by
  classical
  dsimp only
  let := coefficientScalarModelZero A.scalar
  let F := ME.quotient l E Y ⋙ A.scalar.model.E.mapHomologicalComplex (.up ℤ)
  let G := (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ) ⋙
    ML.quotient l L Y
  let a := OrdinaryScalarTowerProof.directEvaluation l E L ι Y A ME ρ association
  let b (n : ℕ) : G ⋙
      (coefficientSequenceEvaluation l L Y n).mapHomologicalComplex (.up ℤ) ≅
      integralScalarFiniteComplex l E L ι Y n :=
    NatIso.ofComponents (fun P ↦ HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ (completedOrdinaryEvaluation l E L ι Y ML n).app (P.X i))
      (by intro i j _hij; exact
        ((completedOrdinaryEvaluation l E L ι Y ML n).hom.naturality (P.d i j)).symm))
      (by intro P Q f; apply HomologicalComplex.hom_ext; intro i
          exact (completedOrdinaryEvaluation l E L ι Y ML n).hom.naturality (f.f i))
  let e (n : ℕ) := a n ≪≫ (b n).symm
  have hs := OrdinaryScalarTowerProof.directTransition l E L ι Y A ME ρ hρ
    association hassociation
  have he (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) (i : ℤ) :
      ((e (n + 1)).hom.app P).f i ≫
          (coefficientSequenceTransition l L Y (Nat.le_succ n)).app ((G.obj P).X i) =
        (coefficientSequenceTransition l L Y (Nat.le_succ n)).app ((F.obj P).X i) ≫
          (normalizedDVRModuleRes l L Y (Nat.le_succ n)).map
            (((e n).hom.app P).f i) := by
    exact WeilConjectures.successor_square l L Y ((F.obj P).X i) ((G.obj P).X i)
      (fun k ↦ ((integralScalarFiniteComplex l E L ι Y k).obj P).X i)
      (fun k ↦ HomologicalComplex.Hom.isoApp ((a k).app P) i)
      (fun k ↦ HomologicalComplex.Hom.isoApp ((b k).app P) i)
      (fun k U x ↦ (((integralScalarTransition l E L ι Y k).app P).f i).val.app U x)
      (fun k U x ↦ hs P k i U x)
      (fun k U x ↦ completedOrdinaryEvaluation_transition l E L ι Y ML P k i U x) n
  exact WeilConjectures.complexIsoOfSuccessor l L Y F G e he

/-- Scalar extension carries a coherent ordinary quotient presentation to the
ordinary quotient of completed scalar extension, with its tensor-unit coordinates.
Source: Stacks 03EK, 03D7, 06YY and 07A4; scalar association in the quotient
calculation of step 8 of scalar-extension tower coherence.
(blueprint: lem-trf-scalar-ordinary-presentation-coordinates).

Proof: associate completed scalar extension followed by finite reduction with direct
finite scalar extension by uniqueness of normalized tensor adjoints. The unit equation
fixes its tensor generators. Linearity and compatibility of quotient units with the
successor maps identify the transitions. Compare with finite sequence scalar extension
and glue the successor squares into a strict sequence isomorphism on complexes.
Transport it along the given presentation isomorphism. Naturality of the scalar unit
and the prescribed finite presentation comparisons give the displayed coordinate formula.
No flatness is used: the same tensor formulas cover zero complexes, n=0, empty sites,
identity embeddings and ramified coefficient extensions. -/
theorem scalarOrdinaryPresentationCoordinates (Y : Scheme.{u})
    (A : CoefficientExtensionSystems l E L ι Y)
    (ME : CompletionUnit.OrdinaryModel l E Y)
    (ML : CompletionUnit.OrdinaryModel l L Y)
    (ρ : ∀ n, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L Y n ≅
      coefficientSequenceEvaluation l E Y n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι Y A ρ)
    (association : ∀ n, scalarReductionExtension l E Y n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι Y n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι Y A association)
    (F : coefficientSequenceModules l E Y ⥤ coefficientSequenceModules l L Y)
    [F.Additive] (hF : A.scalar.model.E = F)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (a : (ME.quotient l E Y).obj P ≅ C)
    (κ : ∀ n, ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
      (unrestrictedIntegralFiniteComplex l E Y n).obj P)
    (hκ : ∀ n,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
        κ n = (NatIso.mapHomologicalComplex (ME.evaluation n) (.up ℤ)).app P) :
    ∃ v : (F.mapHomologicalComplex (.up ℤ)).obj C ≅
      (ML.quotient l L Y).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P),
      ∀ (n : ℕ) (i : ℤ) (U : Y.ProEtᵒᵖ) (x : (P.X i).val.obj U)
        (y : (F.obj (C.X i)).val.obj (op (n, U.unop))),
        HEq y ((A.scalar.ordinaryAdjunction.unit.app (C.X i)).val.app
          (op (n, U.unop)) (integralComparisonSequenceSection l E Y (C.X i) n U
            (((κ n).inv.f i).val.app U
              (unrestrictedIntegralTensorSection l E Y n (P.X i) U 1 x)))) →
        (((coefficientSequenceEvaluation l L Y n).map (v.hom.f i) ≫
            (ML.evaluation n).hom.app ((integralOrdinaryScalar l E L ι Y).obj (P.X i))).val.app
          U (coefficientEvaluationSection l L Y (F.obj (C.X i)) n U y)) =
        unrestrictedIntegralTensorSection l L Y n
          ((integralOrdinaryScalar l E L ι Y).obj (P.X i)) U 1
          (integralOrdinaryTensorSection l E L ι Y (P.X i) U 1 x) := by
  subst F
  let := coefficientScalarModelZero A.scalar
  obtain ⟨β, hβ⟩ := strictScalarAssociation l E L ι Y A ME ML ρ hρ
    association hassociation
  let v := (A.scalar.model.E.mapHomologicalComplex (.up ℤ)).mapIso a.symm ≪≫ β.app P
  refine ⟨v, ?_⟩
  intro n i U x y hy
  let w := integralComparisonSequenceSection l E Y (C.X i) n U
    (((κ n).inv.f i).val.app U
      (unrestrictedIntegralTensorSection l E Y n (P.X i) U 1 x))
  let z := CoefficientExtensionAssociation.quotientUnitSection l E Y ME (P.X i) n U x
  have hp := OrdinaryScalarTowerProof.presentationUnit l E Y ME P C a κ hκ n i U x
  have hn := congrArg (fun f ↦ f.val.app (op (n, U.unop)) w)
    (A.scalar.ordinaryAdjunction.unit.naturality (a.inv.f i))
  change (A.scalar.ordinaryAdjunction.unit.app (ME.tensor.obj (P.X i))).val.app
      (op (n, U.unop)) ((a.inv.f i).val.app (op (n, U.unop)) w) =
    (A.scalar.model.E.map (a.inv.f i)).val.app (op (n, U.unop))
      ((A.scalar.ordinaryAdjunction.unit.app (C.X i)).val.app (op (n, U.unop)) w) at hn
  rw [hp] at hn
  have hu : coefficientEvaluationSection l L Y
      (A.scalar.model.E.obj (ME.tensor.obj (P.X i))) n U
      ((A.scalar.model.E.map (a.inv.f i)).val.app (op (n, U.unop)) y) =
      CoefficientExtensionAssociation.evaluatedUnitSection l E L ι Y A ρ
        (ME.tensor.obj (P.X i)) n U z := by
    rw [eq_of_heq hy, ← hn]
    exact eq_of_heq ((OrdinaryScalarTowerProof.evaluation_section_heq l L
      (A.scalar.model.E.obj (ME.tensor.obj (P.X i))) n U _).trans
      (CoefficientExtensionAssociation.evaluatedUnitSection_raw l E L ι Y A ρ hρ
        (ME.tensor.obj (P.X i)) n U z).symm)
  have hh := congrArg (fun k ↦ (k.f i).val.app U
    (CoefficientExtensionAssociation.evaluatedUnitSection l E L ι Y A ρ
      (ME.tensor.obj (P.X i)) n U z)) (hβ P n)
  change ((coefficientSequenceEvaluation l L Y n).map ((β.hom.app P).f i)).val.app U
      (CoefficientExtensionAssociation.evaluatedUnitSection l E L ι Y A ρ
        (ME.tensor.obj (P.X i)) n U z) =
    ((completedOrdinaryEvaluation l E L ι Y ML n).inv.app (P.X i)).val.app U
      (((OrdinaryScalarTowerProof.finiteComparison l E L ι Y A ME ρ association n).hom.app
        (P.X i)).val.app U
          (CoefficientExtensionAssociation.evaluatedUnitSection l E L ι Y A ρ
            (ME.tensor.obj (P.X i)) n U z)) at hh
  have hf := OrdinaryScalarTowerProof.finiteComparison_unit l E L ι Y A ME ρ
    association hassociation (P.X i) n U 1 x
  rw [one_smul] at hf
  rw [hf, completedOrdinaryEvaluation_inverse, one_smul] at hh
  change ((ML.evaluation n).hom.app _).val.app U
    (((coefficientSequenceEvaluation l L Y n).map
      ((A.scalar.model.E.map (a.inv.f i)) ≫ (β.hom.app P).f i)).val.app U
        (coefficientEvaluationSection l L Y (A.scalar.model.E.obj (C.X i)) n U y)) = _
  rw [Functor.map_comp]
  change ((ML.evaluation n).hom.app _).val.app U
    (((coefficientSequenceEvaluation l L Y n).map ((β.hom.app P).f i)).val.app U
      (((coefficientSequenceEvaluation l L Y n).map
        (A.scalar.model.E.map (a.inv.f i))).val.app U
          (coefficientEvaluationSection l L Y (A.scalar.model.E.obj (C.X i)) n U y))) = _
  rw [OrdinaryScalarTowerProof.evaluation_map_section]
  erw [hu, hh]
  exact (CoefficientExtensionAssociation.quotientUnitSection_evaluation l L Y ML
    ((integralOrdinaryScalar l E L ι Y).obj (P.X i)) n U
    (integralOrdinaryTensorSection l E L ι Y (P.X i) U 1 x)).trans
      (OrdinaryScalarTowerProof.finiteUnit_eq l L Y
        ((integralOrdinaryScalar l E L ι Y).obj (P.X i)) n U
        (integralOrdinaryTensorSection l E L ι Y (P.X i) U 1 x))

end WeilConjectures.ScalarExtensionTower
