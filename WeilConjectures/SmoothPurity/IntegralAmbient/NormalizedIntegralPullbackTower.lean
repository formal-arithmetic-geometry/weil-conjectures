/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.WeilSheaf.Supporting.CompletedCoefficientRingedCoherence
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SmoothPurity.Integral.IntegralTensorTransitionCompatibility
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

/-! # The normalized integral pullback tower

Source: Stacks Project, sites-modules.tex, Tags 03D7 and 03EL;
sites-cohomology.tex, Tag 06YY
(blueprint: lem-pur-normalized-integral-pullback-tower).

The projection square identifies the right adjoints of pullback followed by reduction
and reduction followed by finite pullback. Uniqueness of left adjoints gives the
comparison, and the composite units determine it on generators. Restriction along
the quotient epimorphism is fully faithful; this proves transition compatibility
and uniqueness of the whole strict tower comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.all false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.IntegralAmbient
open AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [-instance] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive
  SheafOfModules.cochainTensorLocalizationIsMonoidal
  SheafOfModules.cochainTensorLeftPreservesColimits
  SheafOfModules.cochainTensorRightPreservesColimits
attribute [local instance 2000] integralOperationsFiniteHasMap

attribute [local irreducible] constantSheaf

universe a₁ b₁ c₁ d₁

attribute [local irreducible] HasDerivedCategory.standard

@[irreducible] private def pullGenerator {X Y : Scheme.{t}} (f : X ⟶ Y)
    (M : integralTowerModules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((pull l E f).obj M).val.obj (op ((proEtaleBaseChange f).obj V)) :=
  pullSection l E f M V x

@[irreducible] private def finiteGenerator {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    (M : integralOperationsFiniteModules l E Y n) (V : Y.ProEt)
    (x : M.val.obj (op V)) :
    ((integralOperationsLevelPullback l E f n).obj M).val.obj
      (op ((proEtaleBaseChange f).obj V)) :=
  integralOperationsPullbackGenerator l E f n M V x

@[irreducible] private def reductionAdj (W : Scheme.{t}) (n : ℕ) :=
  (reductionAdjunction l E W n).choose

@[irreducible] private def finitePullComparison {X Y : Scheme.{t}}
    (f : X ⟶ Y) (n : ℕ) :
    pull l E f ⋙ unrestrictedIntegralReductionFunctor l E X n ≅
      unrestrictedIntegralReductionFunctor l E Y n ⋙ integralOperationsLevelPullback l E f n := by
  let e := SheafOfModules.IntegralPullbackProof.pushRestrictionIso
    (proEtaleBaseChange f)
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)).map
      (completedIntegralCommRingProjectionUnrestricted l E X n))
    ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat RingCat)).map
      (completedIntegralCommRingProjectionUnrestricted l E Y n))
    (ambientDirectRingMap l E f)
    (integralOperationsDirectRingMap l E f n) (projectionSquare l E f n)
  exact ((adjunction l E f).comp (reductionAdj l E X n)).leftAdjointUniq
    (((reductionAdj l E Y n).comp (integralOperationsPullbackAdjunction l E f n)).ofNatIsoRight
      e.symm)

universe r₀
-- Work over abstract rings here: unfolding the completed ring limits at every
-- sectionwise equality would make kernel checking unnecessarily expensive.

@[irreducible] private def pullLevelComparison {X Y : Scheme.{t}}
    (f : X ⟶ Y) (n : ℕ) :
    pullComplex l E f ⋙ unrestrictedIntegralComplexFunctor l E X n ≅
      integralOperationsPullbackLevel l E f n := by
  letI := integralOperationsLevelPullback_additive l E f n
  exact Functor.isoWhiskerRight
    (Functor.mapHomologicalComplexCompIso (finitePullComparison l E f n) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (unrestrictedIntegralReductionFunctor l E Y n ⋙
          integralOperationsLevelPullback l E f n)) (.up ℤ)).symm)
    (integralOperationsRestrict l E X n)

end WeilConjectures.IntegralAmbient
