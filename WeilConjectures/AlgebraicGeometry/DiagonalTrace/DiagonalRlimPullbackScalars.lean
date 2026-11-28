/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedConstantTowerPushforwardNormalization
public import WeilConjectures.CategoryTheory.Derived.DerivedTowerCounitProjections
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullback
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.Native.NativeIntegralTateTowerLimit
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootTransitions
import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceOrdinaryLimitEpi
import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Mathlib.CategoryTheory.Localization.Predicate
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalRlimPullbackFormal
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceUnitComparisonIso
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalRlimForgetUnit
import all WeilConjectures.AlgebraicGeometry.Pur.PurRootTowerPreservation
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteTowerLimit
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalTraceCompletedScalarSquare

/-! # Discrete scalar comparisons for the derived-limit pullback mate

Normalization of the derived constant/limit adjunctions of discrete scalar sheaves, epimorphic
transitions and preservation of limits for the coefficient and root-line towers under inverse
image, and the inverse-image mate of the completed scalar square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open AlgebraicGeometry.ProEtale
open SpTowerClasses

/-- The derived constant/limit adjunction of discrete scalar sheaves, normalized on K-injective
towers by the ordinary counit, is computed by the ordinary counit on every complex of towers. -/
theorem diagonalRlim_counitFac (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T] (L : DiagonalRlim (DiagonalMod l T))
    (adj : (Functor.const ℕᵒᵖ : DiagonalMod l T ⥤ ℕᵒᵖ ⥤ DiagonalMod l T).mapDerivedCategory ⊣
      L.R)
    (hCounit : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ DiagonalMod l T) ℤ), I.IsKInjective →
      (Functor.const ℕᵒᵖ : DiagonalMod l T ⥤ ℕᵒᵖ ⥤ DiagonalMod l T).mapDerivedCategory.map
          (L.η.app I) ≫ adj.counit.app (DerivedCategory.Q.obj I) =
        (Functor.const ℕᵒᵖ : DiagonalMod l T ⥤
          ℕᵒᵖ ⥤ DiagonalMod l T).mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ DiagonalMod l T) ⥤ DiagonalMod l T).mapHomologicalComplex (.up ℤ)).obj
            I) ≫
        DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplex (.up ℤ)
            (constLimAdj : (Functor.const ℕᵒᵖ : DiagonalMod l T ⥤ ℕᵒᵖ ⥤ DiagonalMod l T) ⊣
              lim)).counit.app I)) :
    L.CounitFac adj :=
  DiagonalRlim.map_η_comp_counit L adj (exists_isKInjective_tower (DiagonalMod l T)) hCounit

/-- The counit of a derived constant/limit adjunction of discrete scalar sheaves computed by the
ordinary counit commutes with the shifts. -/
theorem diagonalRlim_counit_commShift (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T] (L : DiagonalRlim (DiagonalMod l T))
    (adj : (Functor.const ℕᵒᵖ : DiagonalMod l T ⥤ ℕᵒᵖ ⥤ DiagonalMod l T).mapDerivedCategory ⊣
      L.R)
    (h : L.CounitFac adj) : NatTrans.CommShift adj.counit ℤ :=
  DiagonalRlim.counit_commShift L adj (exists_isKInjective_tower (DiagonalMod l T)) h

/-- The transitions of a restricted coefficient tower are epimorphisms. -/
theorem coefficientTower_transition_epi (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {T : Scheme.{u}}
    [DiagonalTraceLocalizations l T] {c : Chern l E T} {r : Restriction l E T}
    (a : Coefficients l E T c r) (n : ℕ) :
    Epi ((r.F.obj (coefficient T (Arings l E T))).map (homOfLE (Nat.le_succ n)).op) :=
  forgottenTower_epi l T _
    (towerTransitions_of_iso a.coefficientForget (coefficientTransitions_epi l T)) n

/-- The transitions of a restricted root-line tower are epimorphisms when `l` is invertible. -/
theorem lineTower_transition_epi (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {T : Scheme.{u}}
    [DiagonalTraceLocalizations l T] [∀ x : T, Invertible (l : T.residueField x)]
    {c : Chern l E T} {r : Restriction l E T} (a : Coefficients l E T c r) (n : ℕ) :
    Epi ((r.F.obj (lineModule l E c)).map (homOfLE (Nat.le_succ n)).op) := by
  have hroot (n : ℕ) : Epi ((roots l T).map (homOfLE (Nat.le_succ n)).op) := by
    simpa only [roots, Scheme.proEtaleRootsOfUnityTower,
      Functor.ofOpSequence_map_homOfLE_succ] using
        Scheme.purTwistRootTransitions_epi T l n
  exact forgottenTower_epi l T _ (towerTransitions_of_iso a.lineForget hroot) n

/-- The tower of the rings `ℤ/l^(n+1)`, with the reduction maps as transitions. -/
noncomputable def residueRingTower (l : ℕ) : ℕᵒᵖ ⥤ CommRingCat.{u + 1} :=
  Functor.ofOpSequence
    (X := fun n ↦ CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))
    (fun n ↦ CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1))) (ZMod (l ^ (n + 1)))).comp
        ULift.ringEquiv.toRingHom)))

/-- The constant sheaves of `residueRingTower` form the tower `Scheme.purTwistZlTower`. -/
noncomputable def residueRingTowerIso (l : ℕ) (X : Scheme.{u}) :
    Scheme.proEtaleCoefficientTower X (residueRingTower l) ≅ Scheme.purTwistZlTower X l :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun f ↦ (NatTrans.ofOpSequence
      (F := Scheme.proEtaleCoefficientTower X (residueRingTower l))
      (G := Scheme.purTwistZlTower X l)
      (fun _ ↦ 𝟙 _) (fun n ↦ by
        simp [Scheme.proEtaleCoefficientTower, residueRingTower, Scheme.purTwistZlTower,
          Scheme.purTwistZlTowerOfUniverses,
          Scheme.purTwistFiniteTransitionOfUniverses])).naturality f)

/-- The underlying sets of pro-étale sheaves of rings preserve limits of towers. -/
theorem forgetRing_preservesTowerLimits (T : Scheme.{u}) :
    PreservesLimitsOfShape ℕᵒᵖ
      (sheafCompose (Scheme.ProEt.topology T) (CategoryTheory.forget CommRingCat.{u + 1})) := by
  have : PreservesLimitsOfShape ℕᵒᵖ
      (sheafCompose (Scheme.ProEt.topology T) (CategoryTheory.forget CommRingCat.{u + 1}) ⋙
        sheafToPresheaf (Scheme.ProEt.topology T) (Type (u + 1))) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1} ⋙
        (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget CommRingCat.{u + 1})))
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf (Scheme.ProEt.topology T) (Type (u + 1)))

/-- The underlying sets of pro-étale abelian sheaves preserve limits of towers. -/
theorem forgetAb_preservesTowerLimits (T : Scheme.{u}) :
    PreservesLimitsOfShape ℕᵒᵖ
      (sheafCompose (Scheme.ProEt.topology T) (CategoryTheory.forget AddCommGrpCat.{u + 1})) := by
  have : PreservesLimitsOfShape ℕᵒᵖ
      (sheafCompose (Scheme.ProEt.topology T) (CategoryTheory.forget AddCommGrpCat.{u + 1}) ⋙
        sheafToPresheaf (Scheme.ProEt.topology T) (Type (u + 1))) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{u + 1})))
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf (Scheme.ProEt.topology T) (Type (u + 1)))

/-- Exact inverse image of discrete scalar sheaves preserves the limit of a tower whose
underlying abelian tower has its limit preserved by abelian inverse image. -/
theorem upperStar_preservesLimit_of_forget (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    (f : X ⟶ S) [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (H : ℕᵒᵖ ⥤ DiagonalMod l S)
    [PreservesLimit (H ⋙ diagonalForget l S) (upperStar AddCommGrpCat.{u + 1} f)] :
    PreservesLimit H (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f) := by
  have : PreservesLimit H (diagonalForget l S ⋙ upperStar AddCommGrpCat.{u + 1} f) :=
    inferInstance
  have : PreservesLimit H
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f ⋙ diagonalForget l X) :=
    preservesLimit_of_natIso _ (forgetPullbackIso l f).symm
  have : (diagonalForget l X).ReflectsIsomorphisms := by
    dsimp [diagonalForget]
    infer_instance
  have : ReflectsLimitsOfShape ℕᵒᵖ (diagonalForget l X) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimit_of_reflects_of_preserves _ (diagonalForget l X)

/-- Exact inverse image of fixed discrete scalar sheaves preserves the limit of the restricted
coefficient tower, the tower of the quotients `ℤ/l^(n+1)`. -/
theorem upperStar_preserves_coefficientTower_limit (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    (f : X ⟶ S) [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {cS : Chern l (ULift.{u} (Padic l)) S} {rS : Restriction l (ULift.{u} (Padic l)) S}
    (aS : Coefficients l (ULift.{u} (Padic l)) S cS rS) :
    IsIso (limit.post (rS.F.obj (coefficient S (Arings l (ULift.{u} (Padic l)) S)))
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)) := by
  let Q := residueRingTower.{u} l
  have (n : ℕᵒᵖ) : NeZero (l ^ (n.unop + 1)) :=
    ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have (n : ℕᵒᵖ) : Finite (Q.obj n) := by
    change Finite (ULift (ZMod (l ^ (n.unop + 1))))
    infer_instance
  let T := Scheme.proEtaleCoefficientTower S Q
  let Ry := sheafCompose (Scheme.ProEt.topology S) (CategoryTheory.forget CommRingCat.{u + 1})
  let Fy := sheafCompose (Scheme.ProEt.topology S) (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let Fx := sheafCompose (Scheme.ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let P := Scheme.proEtaleSheafInverseImage f (Type (u + 1))
  have := forgetRing_preservesTowerLimits S
  have := forgetRing_preservesTowerLimits X
  have := forgetAb_preservesTowerLimits S
  have := forgetAb_preservesTowerLimits X
  have : PreservesLimit T (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}) :=
    Scheme.proEtaleSheafInverseImage_preserves_finite_tower f Q
  have : PreservesLimit T (Ry ⋙ P) :=
    preservesLimit_of_natIso T (Scheme.ringForgetInverseImageIso f)
  have : PreservesLimit (T ⋙ Ry) P :=
    preservesLimit_of_preserves_limit_cone (isLimitOfPreserves Ry (limit.isLimit T))
      (isLimitOfPreserves (Ry ⋙ P) (limit.isLimit T))
  let H := rS.F.obj (coefficient S (Arings l (ULift.{u} (Padic l)) S))
  let e : (H ⋙ diagonalForget l S) ⋙ Fy ≅ T ⋙ Ry :=
    Functor.isoWhiskerRight aS.coefficientForget Fy ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerRight (residueRingTowerIso l S).symm
        (sheafCompose (Scheme.ProEt.topology S) ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}))) Fy ≪≫
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  have : PreservesLimit ((H ⋙ diagonalForget l S) ⋙ Fy) P :=
    preservesLimit_of_iso_diagram P e.symm
  have : PreservesLimit (H ⋙ diagonalForget l S) (Fy ⋙ P) := inferInstance
  have : PreservesLimit (H ⋙ diagonalForget l S)
      (upperStar AddCommGrpCat.{u + 1} f ⋙ Fx) :=
    preservesLimit_of_natIso _ (Scheme.abelianForgetInverseImageIso f).symm
  have : ReflectsLimitsOfShape ℕᵒᵖ Fx := reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : PreservesLimit (H ⋙ diagonalForget l S) (upperStar AddCommGrpCat.{u + 1} f) :=
    preservesLimit_of_reflects_of_preserves _ Fx
  have := upperStar_preservesLimit_of_forget l f H
  infer_instance

/-- Exact inverse image of fixed discrete scalar sheaves preserves the limit of the restricted
root-line tower, the tower of the roots of unity `μ_(l^(n+1))`, when `l` is invertible. -/
theorem upperStar_preserves_lineTower_limit (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    (f : X ⟶ S) [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [∀ x : X, Invertible (l : X.residueField x)] [∀ y : S, Invertible (l : S.residueField y)]
    {cS : Chern l (ULift.{u} (Padic l)) S} {rS : Restriction l (ULift.{u} (Padic l)) S}
    (aS : Coefficients l (ULift.{u} (Padic l)) S cS rS) :
    IsIso (limit.post (rS.F.obj (lineModule l (ULift.{u} (Padic l)) cS))
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)) := by
  let H := rS.F.obj (lineModule l (ULift.{u} (Padic l)) cS)
  have : PreservesLimit (roots l S) (upperStar AddCommGrpCat.{u + 1} f) :=
    Scheme.pur_root_tower_preservation f l
  have : PreservesLimit (H ⋙ diagonalForget l S) (upperStar AddCommGrpCat.{u + 1} f) :=
    preservesLimit_of_iso_diagram _ aS.lineForget.symm
  have := upperStar_preservesLimit_of_forget l f H
  infer_instance

/-- Forgetting the discrete scalars of the restriction of a completed module recovers its
underlying abelian sheaf. -/
def diagonalCompletedRestrictionUnderlying (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    diagonalCompletedRestriction l T ⋙ diagonalForget l T ≅
      SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (Scheme.purTwistZlCompletion T l)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The direct image of completed coefficient modules commutes with the restriction to the
fixed discrete scalars, by an isomorphism which is the identity on sections. -/
theorem diagonalCompletedScalarPush_exists (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    (f : X ⟶ S) :
    ∃ d : Scheme.proEtaleRingModuleDirectImage f
          (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
          (asIso (diagonalCompletedCoefficientMap l f)) ⋙ diagonalCompletedRestriction l S ≅
        diagonalCompletedRestriction l X ⋙
          lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f,
      ∀ (M : DiagonalCompleted l X) (U : S.ProEtᵒᵖ)
        (x : ((Scheme.proEtaleRingModuleDirectImage f
          (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
          (asIso (diagonalCompletedCoefficientMap l f)) ⋙
          diagonalCompletedRestriction l S).obj M).obj.obj U),
        HEq ((d.hom.app M).hom.app U x) x :=
  ⟨diagonalTraceCompletedScalarSquare l f, diagonalTraceCompletedScalarSquare_hom_app_hom_app l f⟩

/-- The inverse-image mate of a section-preserving comparison between completed direct image
and restriction to the fixed discrete scalars is invertible. -/
theorem diagonalCompletedScalarMate_isIso (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    (f : X ⟶ S)
    (d : Scheme.proEtaleRingModuleDirectImage f
          (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
          (asIso (diagonalCompletedCoefficientMap l f)) ⋙ diagonalCompletedRestriction l S ≅
        diagonalCompletedRestriction l X ⋙
          lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
    (hd : ∀ (M : DiagonalCompleted l X) (U : S.ProEtᵒᵖ)
        (x : ((Scheme.proEtaleRingModuleDirectImage f
          (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
          (asIso (diagonalCompletedCoefficientMap l f)) ⋙
          diagonalCompletedRestriction l S).obj M).obj.obj U),
        HEq ((d.hom.app M).hom.app U x) x) :
    IsIso ((mateEquiv (Scheme.proEtaleRingModuleAdjunction f
          (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
          (asIso (diagonalCompletedCoefficientMap l f)))
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)).symm
        (TwoSquare.mk _ _ _ _ d.hom)) := by
  let adjC := Scheme.proEtaleRingModuleAdjunction f
    (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
    (asIso (diagonalCompletedCoefficientMap l f))
  let am := upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f
  let aa := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  let eS := diagonalCompletedRestrictionUnderlying l S
  let eX := diagonalCompletedRestrictionUnderlying l X
  let δ := (mateEquiv adjC am).symm (TwoSquare.mk _ _ _ _ d.hom)
  have hi (M : DiagonalCompleted l S) : IsIso (δ.app M) := by
    have : (diagonalForget l X).ReflectsIsomorphisms := by
      dsimp [diagonalForget]
      infer_instance
    apply (isIso_iff_of_reflects_iso (δ.app M) (diagonalForget l X)).mp
    have hz := diagonalRlimForgetUnit l f ((diagonalCompletedRestriction l S).obj M)
    have hh := Scheme.ringUnitComparison f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) (asIso (diagonalCompletedCoefficientMap l f)) adjC M
    have hde (N : DiagonalCompleted l X) :
        (diagonalForget l S).map (d.hom.app N) ≫
          (lowerStar AddCommGrpCat.{u + 1} f).map (eX.hom.app N) =
        eS.hom.app ((Scheme.proEtaleRingModuleDirectImage f
          (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
          (asIso (diagonalCompletedCoefficientMap l f))).obj N) := by
      ext U x
      exact eq_of_heq (hd N U x)
    have hu := unit_mateEquiv_symm adjC am (TwoSquare.mk _ _ _ _ d.hom) M
    have hu' := congrArg (diagonalForget l S).map hu
    simp only [Functor.map_comp] at hu'
    have hk : (diagonalForget l S).map (am.unit.app ((diagonalCompletedRestriction l S).obj M)) ≫
        (lowerStar AddCommGrpCat.{u + 1} f).map
          ((diagonalForget l X).map (δ.app M) ≫
            eX.hom.app ((DiagonalCoefficients.diagonalRealizationPull l f).obj M)) =
        eS.hom.app M ≫ (SheafOfModules.toSheaf _).map (adjC.unit.app M) := by
      have hu'' : (diagonalForget l S).map
          (am.unit.app ((diagonalCompletedRestriction l S).obj M)) ≫
          (lowerStar AddCommGrpCat.{u + 1} f).map ((diagonalForget l X).map (δ.app M)) =
          (diagonalForget l S).map ((diagonalCompletedRestriction l S).map (adjC.unit.app M)) ≫
          (diagonalForget l S).map (d.hom.app
            ((DiagonalCoefficients.diagonalRealizationPull l f).obj M)) :=
        hu'.symm
      rw [Functor.map_comp, reassoc_of% hu'', hde]
      exact eS.hom.naturality (adjC.unit.app M)
    have hh' : IsIso ((aa.homEquiv _ _).symm
        (eS.hom.app M ≫ (SheafOfModules.toSheaf _).map (adjC.unit.app M))) := by
      rw [aa.homEquiv_naturality_left_symm]
      have : IsIso ((aa.homEquiv _ _).symm
          ((SheafOfModules.toSheaf _).map (adjC.unit.app M))) := hh
      exact IsIso.comp_isIso' inferInstance this
    have := isoOfAdjunct aa _ _ _ hz hh' hk
    exact IsIso.of_isIso_comp_right ((diagonalForget l X).map (δ.app M))
      (eX.hom.app ((DiagonalCoefficients.diagonalRealizationPull l f).obj M))
  exact NatIso.isIso_of_isIso_app δ

end AlgebraicGeometry.ProEtale.DiagonalTrace
