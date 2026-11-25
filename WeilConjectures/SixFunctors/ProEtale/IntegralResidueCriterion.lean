/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.AlgebraicGeometry.CohomologyTorInterval
import all WeilConjectures.AlgebraicGeometry.IntegralConstantModelHeartClosure
import WeilConjectures.AlgebraicGeometry.IntegralModelsStacks
import all WeilConjectures.AlgebraicGeometry.StratifiedTorIntervalDevissage
import WeilConjectures.SixFunctors.ProEtale.IntegralConstantLocalTor
import WeilConjectures.SixFunctors.ProEtale.InternalCompletionStacksComparison
import WeilConjectures.SixFunctors.ProEtale.InternalResidueStacksComparison

/-! # Integral constructibility detected by the actual residue reduction

## References

* [Stacks, Tag 099L](https://stacks.math.columbia.edu/tag/099L)
* [Stacks, Tag 09C1](https://stacks.math.columbia.edu/tag/09C1)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

local instance criterionSiteSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [local irreducible] upperStarFromPoint

local instance criterionAbSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

local instance criterionAbLocallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify in
/-- The residue criterion in the internal continuous coefficient presentation. -/
theorem internal_integral_residue_criterion
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] :
    (∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K ↔
        IsDerivedComplete l E X K ∧
        constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
          ((AdicCompletion.derivedReduction l E X 0).obj K) ∧
        DerivedCategory.finiteTorAmplitude _
          ((AdicCompletion.derivedReduction l E X 0).obj K)) ∧
    constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X =
      (constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X ⊓
        DerivedCategory.finiteTorAmplitude (AdicCompletion.Modules l E X)) := by
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X)
  have : F.IsEquivalence := (Mod.comapEquivalenceOfIsIso _).isEquivalence_functor
  have hc (K : DerivedCategory (AdicCompletion.Modules l E X)) :
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K ↔
        constantModelBoundedConstructible (IntegralModelsStacks.integersObj l E) X
          (F.mapDerivedCategory.obj K) := by
    apply and_congr
    · exact ⟨F.bounded_mapDerivedCategory_obj, F.bounded_of_bounded_mapDerivedCategory_obj⟩
    · apply forall_congr'
      intro q
      have h := constantModel_comap_iff (IntegralConstantModel.pointComparison l E).inv.hom
        X ((DerivedCategory.homologyFunctor _ q).obj K)
      have hi := (constantModelConstructibleFiniteTor_wellDefined
        (IntegralModelsStacks.integersObj l E) X).1
      let := hi
      exact h.symm.trans
        ⟨fun h ↦ ObjectProperty.prop_of_iso _
          ((F.mapDerivedCategoryHomologyFunctorIso q).app K) h,
        fun h ↦ ObjectProperty.prop_of_iso _
          ((F.mapDerivedCategoryHomologyFunctorIso q).app K).symm h⟩
  constructor
  · intro K
    exact (hc K).trans
      (((IntegralModelsStacks.integral_models_stacks l E X).1 _).trans
        (and_congr (internal_completion_stacks_comparison l E X K).symm
          (internal_residue_stacks_comparison l E X K)))
  · funext K
    apply propext
    constructor
    · intro hK
      refine ⟨hK, ?_⟩
      obtain ⟨a, b, hab⟩ := (DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).2 hK.1
      have hvan (q : ℤ) (hq : q ∉ Set.Icc (min a b) b) :
          CategoryTheory.Limits.IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
        by_cases hqa : q < min a b
        · exact (DerivedCategory.isGE_iff K a).mp hab.1 q
            (lt_of_lt_of_le hqa (min_le_left _ _))
        · exact (DerivedCategory.isLE_iff K b).mp hab.2 q (by
            simp only [Set.mem_Icc] at hq
            omega)
      have hH (q : ℤ) : _root_.DerivedCategory.torAmplitudeIn _ (-1) 0
          ((DerivedCategory.singleFunctor _ 0).obj
            ((DerivedCategory.homologyFunctor _ q).obj K)) :=
        torInterval_of_stratified (DerivedNakayama.integerRing l E) (-1) 0
          (fun S M hM ↦ integral_constant_local_tor l E S M hM) X _ (hK.2 q)
      exact ⟨min a b + (-1), b + 0, torAmplitudeIn_of_cohomology_interval X
        (Mon.mk (DerivedNakayama.integerRing l E)) K (min a b) b (-1) 0
        (min_le_right _ _) (by omega) hvan (fun q _ ↦ hH q)⟩
    · exact fun h ↦ h.1

end AlgebraicGeometry.ProEtale
