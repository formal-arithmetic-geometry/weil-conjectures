/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefDualFormulaFiniteTrace
public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryCompletedIntegralPullback
import all WeilConjectures.WeilSheaf.Ordinary.OrdinaryIntegralPullbackConstruction
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # The normalized ordinary pullback completion -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CoefDualFormulaScalarTranspose

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)

set_option linter.unusedSectionVars false in
/-- The two presentations of completed-coefficient direct image agree.
Source: blueprint Step 2, ordinary/completed coefficient identification
(blueprint: def-coef-dual-formula-pull-completion).
Proof: both ring maps have the specified constant-section map after every quotient
projection. The completed-ring limit property identifies the maps. Both pushforwards
are the same sectionwise module pushforward along proEtaleBaseChange f; substitute
the ring-map equality. -/
theorem ordinaryPush_eq :
    ordinaryIntegralModulePush l E f =
      proEtaleRingModuleDirectImage f
        ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f) := by
  have hc : proEtaleRingDirectImageMap f
      (completedIntegralCommRingSheafUnrestricted l E Y)
      (completedIntegralCommRingSheafUnrestricted l E X)
      ((PurCompactSupport.completed l E).pull f) = sfCompletedCoefficientMap l E f := by
    let adj := proEtaleSheafAdjunction f CommRingCat.{u + 1}
    change adj.homEquiv _ _ ((adj.homEquiv _ _).symm _) = _
    exact (adj.homEquiv _ _).apply_symm_apply _
  have hr : ordinaryIntegralDirectRingMap l E f =
      (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (sfCompletedCoefficientMap l E f) := by
    apply (ordinaryIntegralDirectRingMap_existsUnique l E f).unique
    · exact (ordinaryIntegralDirectRingMap_existsUnique l E f).exists.choose_spec
    · intro n
      exact congrArg
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map)
        ((sfCompletedCoefficientMap_existsUnique l E f).exists.choose_spec n)
  have := Scheme.ProEt.isContinuous_overPullback f
  unfold ordinaryIntegralModulePush proEtaleRingModuleDirectImage
  change SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
      (J := ProEt.topology Y) (K := ProEt.topology X)
      (ordinaryIntegralDirectRingMap l E f) =
    SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
      (J := ProEt.topology Y) (K := ProEt.topology X)
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (proEtaleRingDirectImageMap f
            (completedIntegralCommRingSheafUnrestricted l E Y)
            (completedIntegralCommRingSheafUnrestricted l E X)
            ((PurCompactSupport.completed l E).pull f)))
  rw [hc, hr]
  rfl

/-- Canonical comparison of the ordinary module pullback presentations, preserving
adjunction units. Source: blueprint Step 2
(blueprint: def-coef-dual-formula-pull-completion). -/
def ordinaryPullIso :
    proEtaleRingModulePullback f
        ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f) ≅ ordinaryIntegralModulePull l E f :=
  (proEtaleRingModuleAdjunction f
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull f)).leftAdjointUniq
      ((ordinaryIntegralModuleAdjunction l E f).ofNatIsoRight
        (eqToIso (ordinaryPush_eq l E f)))

attribute [local irreducible] ordinaryIntegralModulePull proEtaleRingModulePullback in
/-- The unit-normalized module comparison applied termwise to a cochain complex.
Source: blueprint Step 2
(blueprint: def-coef-dual-formula-pull-completion). -/
def ordinaryPullComplexMap (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ((proEtaleRingModulePullback f
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull f)).mapHomologicalComplex (.up ℤ)).obj P ⟶
        (ordinaryIntegralPullComplex l E f).obj P := by
  refine { f := fun i => (ordinaryPullIso l E f).hom.app (P.X i), comm' := ?_ }
  intro i j _
  exact ((ordinaryPullIso l E f).hom.naturality (P.d i j)).symm

set_option maxHeartbeats 2000000 in
-- Componentwise uniqueness unfolds the two coefficient-category presentations.
attribute [local irreducible] ordinaryIntegralModulePull proEtaleRingModulePullback
  ordinaryIntegralCompletionChain
  integralOperationsPullbackTowerFunctor integralOperationsPullbackComplexFunctor
  integralDerivedPullback integralDerivedPullbackComparison ordinaryPullIso in
/-- The completion map from the projection-formula pullback presentation is fixed on
K-flat representatives by the actual strict quotient augmentation and zero cone coordinate.
Source: blueprint Steps 2 and 11
(blueprint: def-coef-dual-formula-pull-completion).
Proof: use ordinaryPullIso, exact termwise descent of ringed inverse image, and the
quotients-and-zero completion chain. The resolving-class localization uniquely descends
this natural comparison; its component square on K-flats is the displayed equation. -/
theorem pullCompletion_existsUnique :
    ∃! q : PurCompactSupport.pull (PurCompactSupport.completed l E) f ⟶
        integralDerivedPullback.{u, u} l E f,
      ∀ P : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory,
        q.app ((@DerivedCategory.Q (scalarReductionSource.{u, u} l E Y) _ _
          (HasDerivedCategory.standard _)).obj P.obj) ≫
            (integralDerivedPullbackComparison.{u, u} l E f).hom.app P =
          (proEtaleRingDerivedPullbackFactors f
            ((PurCompactSupport.completed l E).ring Y)
            ((PurCompactSupport.completed l E).ring X)
            ((PurCompactSupport.completed l E).pull f)).hom.app P.obj ≫
          (@DerivedCategory.Q (scalarReductionSource.{u, u} l E X) _ _
            (HasDerivedCategory.standard _)).map (ordinaryPullComplexMap l E f P.obj) ≫
          (@DerivedCategory.Q (scalarReductionSource.{u, u} l E X) _ _
            (HasDerivedCategory.standard _)).map (ordinaryIntegralCompletionChain l E f P.obj) := by
  let QX := @DerivedCategory.Q (scalarReductionSource.{u, u} l E X) _ _
    (HasDerivedCategory.standard _)
  let L := integralOperationsGoodLocalization l E Y
  let O := PurCompactSupport.pull (PurCompactSupport.completed l E) f
  let F := integralDerivedPullback.{u, u} l E f
  let e := integralDerivedPullbackComparison.{u, u} l E f
  let α :
      (proEtaleRingModulePullback f
        ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f)).mapHomologicalComplex (.up ℤ) ⟶
        ordinaryIntegralPullComplex l E f :=
    { app := ordinaryPullComplexMap l E f
      naturality := by
        intro P R h
        apply HomologicalComplex.hom_ext
        intro i
        exact (ordinaryPullIso l E f).hom.naturality (h.f i) }
  let β : L ⋙ O ⟶ integralOperationsPullbackOnGood l E f :=
    Functor.whiskerLeft (integralOperationsGoodComplex.{u, u} l E Y).ι
      ((proEtaleRingDerivedPullbackFactors f
        ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f)).hom ≫
      Functor.whiskerRight
        α QX ≫
      Functor.whiskerRight (ordinaryIntegralCompletionNat l E f) QX)
  let ff := Classical.choice (good_whisker_fullyFaithful l E Y
    (DerivedCategory (integralTowerModules l E X)))
  obtain ⟨q, hq, hu⟩ := ordinaryNormalizedComparison_existsUnique L ff O F _ e β
  refine ⟨q, ?_, ?_⟩
  · intro P
    exact hq P
  · intro q' hq'
    apply hu
    intro P
    exact hq' P

/-- The canonical ordinary-to-completed pullback map, with the complete chain normalization.
Source: blueprint Steps 2 and 11
(blueprint: def-coef-dual-formula-pull-completion). -/
def pullCompletion :
    PurCompactSupport.pull (PurCompactSupport.completed l E) f ⟶
      integralDerivedPullback.{u, u} l E f :=
  (pullCompletion_existsUnique l E f).exists.choose

end WeilConjectures.CoefDualFormulaScalarTranspose
