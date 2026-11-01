/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.CategoryTheory.StrictRoosComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.RoosComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.StrictRoosNormalization
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
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
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientPullbackModelExistence
import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientScalarModelExistence
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.ProperBaseChange.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.ProperBaseChange.RingedToposPullbackFilteredColimits
public import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction

/-! # Primitive realization on simultaneous quotient complexes

Source: Stacks 099N(2),(5), 06YS, 0G7E, 0D6D and 0941; the explicit
all-ambient quotient/Roos definitions of completed pullback and scalar extension
(blueprint: lem-trf-primitive-quotient-realization-comparisons).

Natural number n denotes positive exponent n+1. The realization interfaces fix
all representative identifications and the normalized total-limit comparison.
No flatness assumption is made on a homomorphism between quotient rings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe a b r
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace PrimitiveOrdinary
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S T : Sheaf J CommRingCat.{r}}

private abbrev Mod (R : Sheaf J CommRingCat.{r}) :=
  SheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)

private structure Ordinary {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S) where
  E : Mod R ⥤ Mod S
  obj_eq : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M
  map_eq : ∀ {M N} (f : M ⟶ N), E.map f =
    eqToHom (obj_eq M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (obj_eq N).symm
  [additive : E.Additive]

private def tmul {φ : R ⟶ S} (A : Ordinary φ) (P : Mod R) (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : P.val.obj U) : (A.E.obj P).val.obj U :=
  (eqToHom (A.obj_eq P).symm).val.app U
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ P).presheaf).app U
      (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))

private theorem adj_exists {φ : R ⟶ S} (A : Ordinary φ) :
    ∃ adj : A.E ⊣ SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ),
      ∀ P U (x : P.val.obj U), (adj.unit.app P).val.app U x = tmul A P U 1 x := by
  obtain ⟨_, _, h⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨adj, hadj⟩ := h A.E A.obj_eq A.map_eq
  refine ⟨adj, ?_⟩
  intro P U x
  have ht := hadj P (A.E.obj P) (eqToHom (A.obj_eq P).symm) U x
  simp only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at ht
  exact ht

private def adj {φ : R ⟶ S} (A : Ordinary φ) := (adj_exists A).choose

private theorem adj_unit {φ : R ⟶ S} (A : Ordinary φ) (P : Mod R)
    (U : Cᵒᵖ) (x : P.val.obj U) :
    ((adj A).unit.app P).val.app U x = tmul A P U 1 x :=
  (adj_exists A).choose_spec P U x

private theorem tmul_smul {φ : R ⟶ S} (A : Ordinary φ) (P : Mod R)
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : P.val.obj U) :
    tmul A P U s x = s • tmul A P U 1 x := by
  let η := (PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients J S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf φ P)
  change (eqToHom (A.obj_eq P).symm).val.app U
      (η.app U (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
    s • (eqToHom (A.obj_eq P).symm).val.app U
      (η.app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  rw [← ((eqToHom (A.obj_eq P).symm).val.app U).hom.map_smul,
    ← (η.app U).hom.map_smul]
  congr 2
  change (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) =
    (s * 1) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x
  rw [mul_one]

private theorem transpose {φ : R ⟶ S} (A : Ordinary φ)
    (P : Mod R) (N : Mod S) (f : A.E.obj P ⟶ N)
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : P.val.obj U) :
    f.val.app U (tmul A P U s x) =
      s • (show N.val.obj U from ((adj A).homEquiv P N f).val.app U x) := by
  rw [tmul_smul, ← adj_unit]
  rw [Adjunction.homEquiv_unit]
  exact (f.val.app U).hom.map_smul s _

private theorem hom_ext {φ : R ⟶ S} (A : Ordinary φ)
    (P : Mod R) (N : Mod S) (f g : A.E.obj P ⟶ N)
    (h : ∀ U x, f.val.app U (tmul A P U 1 x) =
      g.val.app U (tmul A P U 1 x)) : f = g := by
  apply ((adj A).homEquiv P N).injective
  ext U x
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change f.val.app U (((adj A).unit.app P).val.app U x) =
    g.val.app U (((adj A).unit.app P).val.app U x)
  rw [adj_unit]
  exact h U x

private def comp {φ : R ⟶ S} {ψ : S ⟶ T} {γ : R ⟶ T}
    (hγ : γ = φ ≫ ψ) (A : Ordinary φ) (B : Ordinary ψ) (D : Ordinary γ) :
    A.E ⋙ B.E ≅ D.E :=
  Adjunction.leftAdjointUniq
    (((adj A).comp (adj B)).ofNatIsoRight
      (SheafOfModules.systemScalarRestrictionComposition φ ψ γ hγ)) (adj D)

private def unit {φ : R ⟶ R} (hφ : φ = 𝟙 R) (A : Ordinary φ) : A.E ≅ 𝟭 (Mod R) :=
  Adjunction.leftAdjointUniq
    ((adj A).ofNatIsoRight (SheafOfModules.systemScalarRestrictionUnit φ hφ)) Adjunction.id

attribute [local instance] Ordinary.additive

attribute [local irreducible] adj

attribute [local irreducible] comp

attribute [local irreducible] unit

private theorem flat_of_single_kFlat [EssentiallySmall.{r} C]
    (M : Mod R)
    (hM : CochainComplex.IsKFlatIndependentCoefficients (R := R)
      ((CochainComplex.singleFunctor (Mod R) 0).obj M)) :
    SheafOfModules.IsFlatOnSite (J := J) (R := R) M := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.tensorPreadditive R
  let S := (CochainComplex.singleFunctor (Mod R) 0).obj M
  let T := MonoidalCategory.tensorRight M
  have hp₀ : HomologicalComplex.preservesQuasiIso (koszulTensorFunctor R S) := by
    intro X Y f hf
    exact CategoryTheory.kFlatTensorPreservesQuasiIsoIndependentCoefficients R S hM f hf
  have hp : HomologicalComplex.preservesQuasiIso (T.mapHomologicalComplex (.up ℤ)) :=
    (HomologicalComplex.preservesQuasiIso).prop_of_iso
      (SheafOfModules.FlatSingleDerivedNormalization.collapse R M) hp₀
  have he : exactFunctor _ _ T :=
    (Functor.exactFunctor_iff_preservesQuasiIso T (.up ℤ)
      (i₀ := 0) (i₁ := 1) rfl (by decide)).2 hp
  exact (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R M).symm he

end PrimitiveOrdinary

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
open scoped ChangeOfRings

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] integralScalarReduction

attribute [local irreducible] quotientAssociation

private theorem sequenceExact_iff (W : Scheme.{t})
    (s : ShortComplex (coefficientSequenceModules l E W)) :
    s.Exact ↔ ∀ n : ℕ, (s.map (coefficientSequenceEvaluation l E W n)).Exact := by
  let D := (SemilinearSections.semilinearDerivedSections.{t + 1, t, u}
    (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
    (coefficientSequenceCommRingTransition l E W)).some.systems
  exact D.componentwise s

private theorem sequenceKFlat_of_evaluations (W : Scheme.{t})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hC : ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n)
      (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E W) C := by
  let R := coefficientSequenceCommRingSheaf l E W
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro Z hZ i
  apply (sequenceExact_iff l E W _).2
  intro n
  have hZn : (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
      (.up ℤ)).obj Z).Acyclic := by
    intro j
    exact (hZ j).map (coefficientSequenceEvaluation l E W n)
  have ht := hC n _ hZn
  exact (ht i).of_iso (coefficientEvaluationTensorIso l E W n Z C).symm

private theorem sequenceFlat_of_evaluations (W : Scheme.{t})
    (M : coefficientSequenceModules l E W)
    (hM : ∀ n : ℕ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W n)
      ((coefficientSequenceEvaluation l E W n).obj M)) :
    SheafOfModules.IsFlatOnSite
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) M := by
  let R := coefficientSequenceCommRingSheaf l E W
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.tensorPreadditive R
  let S := (CochainComplex.singleFunctor (coefficientSequenceModules l E W) 0).obj M
  have hs : CochainComplex.IsKFlatIndependentCoefficients (R := R) S := by
    apply sequenceKFlat_of_evaluations l E W S
    intro n
    let B := integralCoefficientCommRingSheaf l E W n
    have hn := SheafOfModules.FlatSingleDerivedNormalization.single_kFlat B
      ((coefficientSequenceEvaluation l E W n).obj M) (hM n)
    exact SheafOfModules.kFlat_iso_independent B
      ((HomologicalComplex.singleMapHomologicalComplex
        (coefficientSequenceEvaluation l E W n) (.up ℤ) 0).app M).symm hn
  exact PrimitiveOrdinary.flat_of_single_kFlat M hs

/-- Primitive realization isomorphisms on the entire ambient derived categories,
with the fixed normalized Roos comparison and every simultaneous quotient
presentation. These are the interfaces whose `realization` fields are alpha
and beta; their normalization fields specify rho and rho composed with the
inverse of the strict association, respectively.

Source: Stacks 099N(2),(5), 06YS, 0G7E, 0D6D, 0941
(blueprint: lem-trf-primitive-quotient-realization-comparisons).
Proof:
1. Choose a flat-term K-flat resolution by lem-pc-kflat-resolution. Change of
   rings preserves those properties at every quotient by
   lem-pur-kflat-change-of-rings. The calculus's reductionModel supplies one
   strict quotient presentation with the actual maps for all m greater than n.
2. Finite constant-coefficient inverse image is exact by
   prop-weil-pbc-proetale-constant-exact. By lem-coef-semilinear-derived-sections
   it computes whole-system inverse image termwise. Restrict the resulting
   tower to completed coefficients. The defining completed pullback is its
   Roos cone, so apply the fixed rho to this very tower. No infinite product
   passes through inverse image.
3. Construct the balanced association and inverse as in
   primitiveQuotientScalarAssociation. They commute with differentials and
   quotient transitions, giving one strict-system chain isomorphism.
4. The system tensor is componentwise on the vertical sequence site; therefore
   the levelwise K-flat reduction system is K-flat as a whole system. Its
   ordinary scalar extension computes derived extension. The association
   identifies its restricted tower with integralScalarTowerFunctor. Apply H
   to its inverse and then the fixed rho. This is beta with the orientation
   specified in IsIntegralComparisonScalarNormalized.
5. For E to L to M both associations multiply the same three coefficients;
   for equal fields use multiplication with inverse insertion of 1. All
   transitions are the actual reductions, so these identities are strict.
6. The formulas commute with every cochain map. Quotient tensors preserve
   quasi-isomorphisms of good inputs, and exact inverse image preserves them.
   Apply lem-pur-flat-roos-functor-descent and the fixed strict Roos comparison.
   This gives natural isomorphisms on all derived morphisms, independent of
   representatives through the specified comparisons. Exact countable
   products are lem-weil-proetale-countable-products-exact. -/
-- STATEMENT-DISPUTED: CoefficientReductionPresentation determines e only after finite
-- derived evaluations. These are conservative, but do not detect equality of morphisms.
-- Replacing e by reduction of a nontrivial automorphism with identity reductions preserves
-- the hypothesis and the generator-normalized q, but changes the required limit equation.
-- See report.md for the derived-complete, nonseparated Z_p-module counterexample.
theorem primitiveQuotientRealizationComparisons
    {X Y : Scheme.{t}} (f : X ⟶ Y) (W : Scheme.{t})
    (_hlX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hlY : ∀ y : Y, IsUnit (l : Y.residueField y))
    (_hlW : ∀ x : W, IsUnit (l : W.residueField x))
    (SY : CoefficientDerivedSystemCalculus l E Y)
    (SW : CoefficientDerivedSystemCalculus l E W)
    (ρX : IntegralComparisonRoosModel l E X)
    (ρW : IntegralComparisonRoosModel l L W) :
    Nonempty (IntegralComparisonPullbackModel l E f SY ρX) ∧
      Nonempty (IntegralComparisonScalarModel l E L ι W SW ρW) := by
  exact ⟨primitiveQuotientPullbackModelExistence l E f _hlX _hlY SY ρX,
    primitiveQuotientScalarModelExistence l E L ι W _hlW SW ρW⟩

end WeilConjectures
