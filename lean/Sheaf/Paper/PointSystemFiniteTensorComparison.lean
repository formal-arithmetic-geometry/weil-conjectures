/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Paper.PointRestrictionSystemChainMap
import all Sheaf.Paper.PointRestrictionSystemChainMap
import all Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison
import Sheaf.AlgebraicGeometry.ProEtale.FiniteComparisonIsomorphism

/-! # Normalized finite tensor comparison

Source: Stacks Tags 03CZ, 03EK and 0941; the tensor-transition step of
`lem-trf-point-system-transport-descent`.
(blueprint: lem-trf-point-system-finite-tensor-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointSystemTensorTransition
variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  CategoryTheory.sheafCompose coefficientSequenceEvaluation isoSectionwiseModuleInverseImage
  CategoryTheory.Functor.sheafPushforwardContinuous coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem

private abbrev pull := PointRestrictionSystem.pull D l E g
private abbrev sequenceRing := PointRestrictionSystem.sequenceRing D l E
private abbrev tensorPull (n : ℕ) := integralOperationsLevelPullback.{t, u} l E g n
private abbrev tensorLevel (n : ℕ) :=
  coefficientSequenceEvaluation l E (Spec (.of D.k)) n ⋙ tensorPull D l E g n ⋙
    scalarReductionRestriction l E (Spec (.of D.k)) n
private def insertion (n : ℕ) (M : coefficientSequenceModules l E (Spec (.of D.k)))
    (U : (Spec (.of D.k)).ProEt)
    (x : M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U))) :
    ((tensorPull D l E g n).obj
      ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)).val.obj (op U) :=
  (((tensorPull D l E g n).obj
      ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)).val.map
    (proEtaleIsoCommaArrow g U).op)
      (integralOperationsPullbackGenerator l E g n
        ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)
        ((proEtaleIsoPostcompose g).obj U) x)

private instance finitePullAdditive (n : ℕ) :
    (inverseImageFiniteModules.{t, u} l E g n).Additive :=
  (isoSectionwiseModuleInverseImage_exact g (inverseImageFiniteCoefficientMap l E g n)).1
private instance tensorPullAdditive (n : ℕ) : (tensorPull D l E g n).Additive :=
  integralOperationsLevelPullback_additive l E g n

private def finiteComparisonMap (n : ℕ) :
    inverseImageFiniteModules.{t, u} l E g n ⟶ tensorPull D l E g n :=
  finiteModuleComparison l E g n

private theorem finiteComparisonMap_normalization (n : ℕ)
    (M : integralOperationsFiniteModules l E (Spec (.of D.k)) n)
    (U : (Spec (.of D.k)).ProEt)
    (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    ((finiteComparisonMap D l E g n).app M).val.app (op U) x =
      (((tensorPull D l E g n).obj M).val.map
        (proEtaleIsoCommaArrow g U).op)
        (integralOperationsPullbackGenerator l E g n M
          ((proEtaleIsoPostcompose g).obj U) x) := rfl

attribute [local irreducible] finiteComparisonMap

private instance finiteComparisonMap_isIso (n : ℕ) :
    IsIso (finiteComparisonMap D l E g n) := by
  let := tensorPullAdditive D l E g n
  let : (tensorPull D l E g n).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive (tensorPull D l E g n)
  have (M : integralOperationsFiniteModules l E (Spec (.of D.k)) n) :
      IsIso ((finiteComparisonMap D l E g n).app M) := by
    let K := (HomologicalComplex.single
      (integralOperationsFiniteModules l E (Spec (.of D.k)) n) (.up ℤ) 0).obj M
    have he : inverseImageFiniteComparisonComplex l E g n K =
        ((finiteComparisonMap D l E g n).mapHomologicalComplex (.up ℤ)).app K := by
      apply (inverseImageFiniteComparison_existsUnique l E g n K).unique
      · exact (inverseImageFiniteComparison_existsUnique l E
          g n K).exists.choose_spec
      · intro i U x
        exact finiteComparisonMap_normalization D l E g n (K.X i) U x
    have hi := inverseImageFiniteComparisonComplex_isIso l E g n K
    rw [he] at hi
    exact inferInstanceAs
      (IsIso ((((finiteComparisonMap D l E g n).mapHomologicalComplex (.up ℤ)).app K).f 0))
  
  exact NatIso.isIso_of_isIso_app (finiteComparisonMap D l E g n)

/-- The tensor-unit comparison is already an isomorphism on ordinary finite modules.
Source: Stacks Tags 03D2, 03D6 and 00WX; finite-comparison step of point-system transport.
(blueprint: lem-trf-point-system-finite-tensor-comparison).
Proof: apply the recorded complex comparison to a single-term complex in degree zero.
Its prescribed values identify it with the termwise ordinary tensor-unit map.
Evaluation at zero proves each component invertible, hence the natural map is an
isomorphism. Every section has the stated image, which also proves uniqueness. -/
theorem finite_tensor_comparison_iso_existsUnique (n : ℕ) :
    ∃! e : inverseImageFiniteModules.{t, u} l E g n ≅
        integralOperationsLevelPullback.{t, u} l E g n,
      ∀ (M : integralOperationsFiniteModules l E (Spec (.of D.k)) n)
        (U : (Spec (.of D.k)).ProEt)
        (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        (e.hom.app M).val.app (op U) x =
          (((integralOperationsLevelPullback.{t, u} l E g n).obj M).val.map
            (proEtaleIsoCommaArrow g U).op)
            (integralOperationsPullbackGenerator l E g n M
              ((proEtaleIsoPostcompose g).obj U) x) := by
  refine ⟨asIso (finiteComparisonMap D l E g n), ?_, ?_⟩
  · intro M U x
    exact finiteComparisonMap_normalization D l E g n M U x
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (he M U.unop x).trans
      (finiteComparisonMap_normalization D l E g n M U.unop x).symm

end WeilConjectures.PointSystemTensorTransition
