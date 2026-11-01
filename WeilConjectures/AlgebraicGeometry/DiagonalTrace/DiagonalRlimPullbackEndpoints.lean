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
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
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
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
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
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalTraceCompletedScalarSquare
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalRlimCompletedScalarMate
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalRlimTowerLimitPreservation
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalRlimVaryingScalarMate
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceUnitComparisonIso
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Kummer.TowerKummerPullbackTranspose
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.CategoryTheory.SmoothBaseChange.TowerDerivedEvaluationNormalization
public import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients

/-! # Derived-limit pullback comparison with normalized endpoints
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-diagonal-tower/
`sk-prop-diagonal-tower-coefficients.proof.md`, paragraph (3), constant-system/right-derived-limit
comparison and its coefficient/root isomorphism
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u a b c d va vb vc vd wa wb wc wd
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open AlgebraicGeometry.ProEtale
open SpTowerClasses

/-- The actual exact inverse image of fixed discrete scalar sheaves.
Source: blueprint coefficient proof (3)
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints). -/
abbrev diagonalRlimPull (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S] :
    DiagonalMod l S ⥤ DiagonalMod l X :=
  upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f

/-- Its strict termwise tower functor.
Source: blueprint coefficient proof (3)
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints). -/
abbrev diagonalRlimTowerPull (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S] :
    DiagonalSystems l S ⥤ DiagonalSystems l X :=
  (Functor.whiskeringRight ℕᵒᵖ (DiagonalMod l S) (DiagonalMod l X)).obj
    (diagonalRlimPull l f)

/-- Evaluation after termwise pullback, induced by the ordinary termwise identity.
Source: blueprint coefficient proof (3)
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints). -/
def diagonalRlimPullbackEvaluation (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S] (n : ℕ) :
    (diagonalRlimTowerPull l f).mapDerivedCategory ⋙
      ((evaluation ℕᵒᵖ (DiagonalMod l X)).obj (op n)).mapDerivedCategory ≅
    ((evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n)).mapDerivedCategory ⋙
      (diagonalRlimPull l f).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (diagonalRlimTowerPull l f)
    ((evaluation ℕᵒᵖ (DiagonalMod l X)).obj (op n))).symm ≪≫
  Functor.mapDerivedCategoryNatIso (eqToIso rfl) ≪≫
  Functor.mapDerivedCategoryCompIso
    ((evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n)) (diagonalRlimPull l f)

/-- The mate uses the canonical identity-on-components constant-tower interchange.
Source: blueprint coefficient proof (3)
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints). -/
def diagonalRlimPullbackMate (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (LX : DiagonalRlim (DiagonalMod l X)) (LS : DiagonalRlim (DiagonalMod l S))
    (adjX : (Functor.const ℕᵒᵖ : DiagonalMod l X ⥤ DiagonalSystems l X).mapDerivedCategory ⊣ LX.R)
    (adjS : (Functor.const ℕᵒᵖ : DiagonalMod l S ⥤ DiagonalSystems l S).mapDerivedCategory ⊣ LS.R) :
    LS.R ⋙ (diagonalRlimPull l f).mapDerivedCategory ⟶
      (diagonalRlimTowerPull l f).mapDerivedCategory ⋙ LX.R :=
  (mateEquiv adjS adjX (TwoSquare.mk _ _ _ _
    (ringedConstantTowerPullback (diagonalRlimPull l f)).inv)).natTrans

/-- The full pulled cone, using the canonical constant-tower interchange.
Source: blueprint coefficient proof (3), ordinary cone normalization
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints). -/
def diagonalRlimPulledCone (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (M : DiagonalMod l S) (H : DiagonalSystems l S)
    (π : (Functor.const ℕᵒᵖ).obj M ⟶ H) :
    (Functor.const ℕᵒᵖ).obj ((diagonalRlimPull l f).obj M) ⟶
      (diagonalRlimTowerPull l f).obj H :=
  (Functor.compConstIso ℕᵒᵖ (diagonalRlimPull l f)).hom.app M ≫
    (diagonalRlimTowerPull l f).map π

/-- Pull back an exact scalar cone, retaining the canonical derived composition maps.
Source: blueprint coefficient proof (3), scalar restriction and endpoint cones
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints). -/
def diagonalRlimPulledScalarConeMap (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    (f : X ⟶ S) [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (LX : DiagonalRlim (DiagonalMod l X))
    (r : Restriction l (ULift.{u} (Padic l)) S)
    (M : DiagonalCompleted l S) (N : Systems S (Arings l (ULift.{u} (Padic l)) S))
    (π : (Functor.const ℕᵒᵖ).obj ((diagonalCompletedRestriction l S).obj M) ⟶ r.F.obj N) :
    (diagonalCompletedUnderlying l S ⋙ (diagonalRlimPull l f).mapDerivedCategory).obj
        ((DerivedCategory.singleFunctor (DiagonalCompleted l S) 0).obj M) ⟶
      (r.F.mapDerivedCategory ⋙ (diagonalRlimTowerPull l f).mapDerivedCategory ⋙ LX.R).obj
        ((DerivedCategory.singleFunctor (Systems S (Arings l (ULift.{u} (Padic l)) S))
          0).obj N) :=
  (Functor.mapDerivedCategoryCompIso (diagonalCompletedRestriction l S)
    (diagonalRlimPull l f)).inv.app _ ≫
  exactConeComparison (diagonalCompletedRestriction l S ⋙ diagonalRlimPull l f)
    (r.F ⋙ diagonalRlimTowerPull l f) LX M N
    (diagonalRlimPulledCone l f _ _ π) ≫
  LX.R.map ((Functor.mapDerivedCategoryCompIso r.F
    (diagonalRlimTowerPull l f)).hom.app _)

/-- Canonical localization of an exact scalar/pullback square.
Source: blueprint coefficient proof (3), exact restriction squares
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints). -/
def diagonalRlimExactSquare
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
    [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wd} D]
    (U : A ⥤ B) (F : B ⥤ D) (G : A ⥤ C) (V : C ⥤ D)
    [U.Additive] [F.Additive] [G.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (s : U ⋙ F ≅ G ⋙ V) :
    U.mapDerivedCategory ⋙ F.mapDerivedCategory ≅
      G.mapDerivedCategory ⋙ V.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso U F).symm ≪≫
    Functor.mapDerivedCategoryNatIso s ≪≫ Functor.mapDerivedCategoryCompIso G V

/-- Localize the varying scalar square using its recorded exact inverse image.
Source: blueprint coefficient proof (3), varying scalar restriction
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints). -/
def diagonalRlimVaryingSquare (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    (f : X ⟶ S) [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (b : SpTowerShriek.Base l (ULift.{u} (Padic l)))
    (g : SpTowerShriek.Geometry l (ULift.{u} (Padic l)) b f)
    (rS : Restriction l (ULift.{u} (Padic l)) S)
    (rX : Restriction l (ULift.{u} (Padic l)) X)
    (v : rS.F ⋙ diagonalRlimTowerPull l f ≅ g.pull ⋙ rX.F) :
    rS.F.mapDerivedCategory ⋙ (diagonalRlimTowerPull l f).mapDerivedCategory ≅
      (SpTowerShriek.pull l (ULift.{u} (Padic l)) b g) ⋙ rX.F.mapDerivedCategory := by
  letI := g.pullAdditive
  letI := g.pullLimits
  letI := g.pullColimits
  letI := rS.additive
  letI := rX.additive
  letI := rS.limits
  letI := rX.limits
  letI := rS.colimits
  letI := rX.colimits
  exact diagonalRlimExactSquare rS.F (diagonalRlimTowerPull l f) g.pull rX.F v

private theorem mate_commShift
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') {F : A ⥤ C} {G : B ⥤ D}
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    [L.CommShift ℤ] [R.CommShift ℤ] [L'.CommShift ℤ] [R'.CommShift ℤ]
    [F.CommShift ℤ] [G.CommShift ℤ] [adj.CommShift ℤ] [adj'.CommShift ℤ]
    (δ : F ⋙ L' ⟶ L ⋙ G) [NatTrans.CommShift δ ℤ] :
    NatTrans.CommShift (mateEquiv adj adj' δ).natTrans ℤ := by
  dsimp only [mateEquiv, Equiv.coe_fn_mk, TwoSquare.mk, TwoSquare.natTrans]
  infer_instance

private theorem exact_square_commShift
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
    [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wd} D]
    (U : A ⥤ B) (F : B ⥤ D) (G : A ⥤ C) (V : C ⥤ D)
    [U.Additive] [F.Additive] [G.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (s : U ⋙ F ≅ G ⋙ V) :
    NatTrans.CommShift (diagonalRlimExactSquare U F G V s).hom ℤ := by
  dsimp only [diagonalRlimExactSquare, Iso.trans_hom, Iso.symm_hom]
  infer_instance

private theorem counit_on_complexes
    {A : Type a} [Category.{va} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wa} (ℕᵒᵖ ⥤ A)]
    [CategoryTheory.Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    (L : DiagonalRlim A)
    (adj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣ L.R)
    (h : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ), I.IsKInjective →
      (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory.map (L.η.app I) ≫
          adj.counit.app (DerivedCategory.Q.obj I) =
        (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplex (.up ℤ)
            (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A) ⊣ lim)).counit.app I))
    (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory.map (L.η.app K) ≫
        adj.counit.app (DerivedCategory.Q.obj K) =
      (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom.app
        (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((Adjunction.mapHomologicalComplex (.up ℤ)
          (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A) ⊣ lim)).counit.app K) := by
  let C := (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A)
  let lc := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)
  let α : lc ⋙ DerivedCategory.Q ⋙ C.mapDerivedCategory ⟶ DerivedCategory.Q :=
    Functor.whiskerRight L.η C.mapDerivedCategory ≫
      Functor.whiskerLeft DerivedCategory.Q adj.counit
  let β : lc ⋙ DerivedCategory.Q ⋙ C.mapDerivedCategory ⟶ DerivedCategory.Q :=
    Functor.whiskerLeft lc C.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight
        ((constLimAdj : C ⊣ lim).mapHomologicalComplex (.up ℤ)).counit DerivedCategory.Q
  obtain ⟨I, hI, q, _, hq⟩ :=
    CategoryTheory.Abelian.HasKInjectiveResolutions.exists_isKInjective K
  have := hq
  change α.app K = β.app K
  apply (cancel_mono (DerivedCategory.Q.map q)).1
  rw [← α.naturality, ← β.naturality]
  exact congrArg (fun z ↦ (lc ⋙ DerivedCategory.Q ⋙ C.mapDerivedCategory).map q ≫ z)
    (h I hI)

private theorem constant_adj_commShift
    {A : Type a} [Category.{va} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wa} (ℕᵒᵖ ⥤ A)]
    (L : DiagonalRlim A)
    (adj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣ L.R)
    (h : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ),
      (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory.map (L.η.app I) ≫
          adj.counit.app (DerivedCategory.Q.obj I) =
        (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplex (.up ℤ)
            (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A) ⊣ lim)).counit.app I))
    : adj.CommShift ℤ := by
  let C := (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A)
  let Ch := C.mapHomologicalComplex (.up ℤ)
  let Rh := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)
  let ah := (constLimAdj : C ⊣ lim).mapHomologicalComplex (.up ℤ)
  let : C.mapDerivedCategory.IsLeftDerivedFunctor C.mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso A (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ C.mapDerivedCategoryFactors
  have hn : ∀ M : CochainComplex A ℤ,
      adj.unit.app (DerivedCategory.Q.obj M) ≫
          L.R.map (C.mapDerivedCategoryFactors.hom.app M) =
        DerivedCategory.Q.map (ah.unit.app M) ≫ L.η.app (Ch.obj M) := by
    intro M
    apply ((adj.homEquiv _ _).symm).injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    erw [adj.counit.naturality (C.mapDerivedCategoryFactors.hom.app M)]
    erw [← Category.assoc, adj.left_triangle_components, Category.id_comp]
    erw [h (Ch.obj M)]
    erw [C.mapDerivedCategoryFactors.hom.naturality_assoc (ah.unit.app M)]
    simp only [Functor.comp_map, ← DerivedCategory.Q.map_comp]
    change C.mapDerivedCategoryFactors.hom.app M =
      C.mapDerivedCategoryFactors.hom.app M ≫
        DerivedCategory.Q.map (Ch.map (ah.unit.app M) ≫ ah.counit.app (Ch.obj M))
    rw [ah.left_triangle_components]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  let := Functor.IsLeftDerivedFunctor.isRightKanExtension C.mapDerivedCategory
    C.mapDerivedCategoryFactors.hom (HomologicalComplex.quasiIso A (.up ℤ))
  exact Adjunction.CommShift.mk' adj ℤ
    (normalized_unit_commShift DerivedCategory.Q DerivedCategory.Q Ch Rh
      C.mapDerivedCategory L.R ah adj C.mapDerivedCategoryFactors.hom L.η hn)

private theorem single_counit
    {A : Type a} [Category.{va} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wa} (ℕᵒᵖ ⥤ A)]
    (L : DiagonalRlim A)
    (adj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣ L.R)
    (h : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ),
      (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory.map (L.η.app I) ≫
          adj.counit.app (DerivedCategory.Q.obj I) =
        (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplex (.up ℤ)
            (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A) ⊣ lim)).counit.app I))
    (H : ℕᵒᵖ ⥤ A) :
    (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory.map
        (diagonalOrdinaryRlim L H) ≫
      adj.counit.app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj H) =
    ((Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategorySingleFunctor 0).hom.app
        (limit H) ≫
      (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).map
        ((constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A) ⊣ lim).counit.app H) := by
  let C := (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A)
  let R := (lim : (ℕᵒᵖ ⥤ A) ⥤ A)
  let a : C ⊣ R := constLimAdj
  let P := (HomologicalComplex.single (ℕᵒᵖ ⥤ A) (.up ℤ) 0).obj H
  let b := (R.mapCochainComplexSingleFunctor 0).inv.app H
  have hb : (C.mapHomologicalComplex (.up ℤ)).map b ≫
        (a.mapHomologicalComplex (.up ℤ)).counit.app P =
      (C.mapCochainComplexSingleFunctor 0).hom.app (R.obj H) ≫
        (HomologicalComplex.single (ℕᵒᵖ ⥤ A) (.up ℤ) 0).map (a.counit.app H) := by
    apply HomologicalComplex.Hom.ext
    funext n
    by_cases hn : n = 0
    · subst n
      simp only [b, P, Functor.mapCochainComplexSingleFunctor,
        HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        Adjunction.mapHomologicalComplex_counit_app_f]
      erw [HomologicalComplex.single_map_f_self]
      simp only [HomologicalComplex.singleObjXSelf,
        HomologicalComplex.singleObjXIsoOfEq, eqToIso.hom, eqToIso.inv, eqToHom_refl]
      simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      erw [CategoryTheory.Functor.map_id, Category.id_comp]
    · exact (C.map_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)).eq_of_src _ _
  simp only [diagonalOrdinaryRlim, DerivedCategory.singleFunctorIsoCompQ,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  erw [L.R.map_id, Category.comp_id]
  change C.mapDerivedCategory.map (DerivedCategory.Q.map b ≫ L.η.app P) ≫ _ = _
  rw [Functor.map_comp, Category.assoc]
  erw [h P, C.mapDerivedCategoryFactors.hom.naturality_assoc]
  simp only [Functor.comp_map]
  erw [← DerivedCategory.Q.map_comp, hb, DerivedCategory.Q.map_comp]
  rw [C.mapDerivedCategorySingleFunctor_hom_app_eq, Category.assoc]
  rfl

private theorem cone_transpose
    {A : Type a} [Category.{va} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wa} (ℕᵒᵖ ⥤ A)]
    (L : DiagonalRlim A)
    (adj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣ L.R)
    (h : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ),
      (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory.map (L.η.app I) ≫
          adj.counit.app (DerivedCategory.Q.obj I) =
        (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplex (.up ℤ)
            (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A) ⊣ lim)).counit.app I))
    (H : ℕᵒᵖ ⥤ A) (c : Cone H) :
    (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory.map
        (diagonalTraceConeMap L H c) ≫
      adj.counit.app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj H) =
    ((Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategorySingleFunctor 0).hom.app c.pt ≫
      (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).map c.π := by
  let C := (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A)
  simp only [diagonalTraceConeMap, Functor.map_comp, Category.assoc]
  rw [single_counit L adj h H]
  erw [(C.mapDerivedCategorySingleFunctor 0).hom.naturality_assoc (limit.lift H c)]
  dsimp only [Functor.comp_map]
  rw [← (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).map_comp]
  congr 2
  ext n
  exact limit.lift_π c n

private theorem pull_cone
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    [Abelian A] [Abelian B] [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wa} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{wb} B] [HasDerivedCategory.{wb} (ℕᵒᵖ ⥤ B)]
    (LA : DiagonalRlim A) (LB : DiagonalRlim B)
    (adjA : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣ LA.R)
    (adjB : (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategory ⊣ LB.R)
    (ha : ∀ (H : ℕᵒᵖ ⥤ A) (c : Cone H),
      (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory.map
          (diagonalTraceConeMap LA H c) ≫
        adjA.counit.app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj H) =
      ((Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategorySingleFunctor 0).hom.app c.pt ≫
        (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).map c.π)
    (hb : ∀ (H : ℕᵒᵖ ⥤ B) (c : Cone H),
      (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategory.map
          (diagonalTraceConeMap LB H c) ≫
        adjB.counit.app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) =
      ((Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategorySingleFunctor 0).hom.app c.pt ≫
        (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).map c.π)
    (G : B ⥤ A) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : ℕᵒᵖ ⥤ B) (c : Cone H) :
    let W := (Functor.whiskeringRight ℕᵒᵖ B A).obj G
    let β := (mateEquiv adjB adjA
      (TwoSquare.mk _ _ _ _ (ringedConstantTowerPullback G).inv)).natTrans
    G.mapDerivedCategory.map (diagonalTraceConeMap LB H c) ≫
        β.app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) ≫
        LA.R.map ((W.mapDerivedCategorySingleFunctor 0).hom.app H) =
      (G.mapDerivedCategorySingleFunctor 0).hom.app c.pt ≫
        diagonalTraceConeMap LA (W.obj H) (G.mapCone c) := by
  let CA := (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A)
  let CB := (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B)
  let W := (Functor.whiskeringRight ℕᵒᵖ B A).obj G
  let ρ := (ringedConstantTowerPullback G).inv
  let β := (mateEquiv adjB adjA (TwoSquare.mk _ _ _ _ ρ)).natTrans
  have hρ : ρ = (Functor.mapDerivedCategorySquareIso
      (Functor.compConstIso ℕᵒᵖ G)).hom := by
    have he := Functor.mapDerivedCategoryNatIso_symm (Functor.compConstIso ℕᵒᵖ G).symm
    simp only [Iso.symm_symm_eq] at he
    dsimp only [ρ, ringedConstantTowerPullback, Functor.mapDerivedCategorySquareIso,
      Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom]
    rw [← he]
    simp only [Category.assoc]
  have hsingle := square_single G CA CB W (Functor.compConstIso ℕᵒᵖ G) c.pt
  rw [← hρ] at hsingle
  have hm := mateEquiv_counit adjB adjA (TwoSquare.mk _ _ _ _ ρ)
    ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)
  apply ((adjA.homEquiv _ _).symm).injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  erw [adjA.counit.naturality ((W.mapDerivedCategorySingleFunctor 0).hom.app H)]
  erw [reassoc_of% hm]
  erw [ρ.naturality_assoc (diagonalTraceConeMap LB H c)]
  dsimp only [Functor.comp_map, Functor.id_map]
  rw [← W.mapDerivedCategory.map_comp_assoc]
  rw [hb H c]
  rw [W.mapDerivedCategory.map_comp]
  have hw := (W.mapDerivedCategorySingleFunctor 0).hom.naturality c.π
  dsimp only [Functor.comp_map] at hw
  simp only [Category.assoc]
  rw [hw]
  rw [reassoc_of% hsingle]
  rw [← (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).map_comp]
  erw [ha (W.obj H) (G.mapCone c)]
  have hp : (Functor.compConstIso ℕᵒᵖ G).hom.app c.pt ≫ W.map c.π =
      (G.mapCone c).π := by
    ext n
    exact Category.id_comp _
  rw [hp]
  rfl

private theorem pull_evaluation_constant
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wa} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{wb} B] [HasDerivedCategory.{wb} (ℕᵒᵖ ⥤ B)]
    (G : B ⥤ A) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (n : ℕᵒᵖ) (M : DerivedCategory B) :
    let _CA := (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A)
    let CB := (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B)
    let EA := (evaluation ℕᵒᵖ A).obj n
    EA.mapDerivedCategory.map ((ringedConstantTowerPullback G).inv.app M) ≫
        (towerDerivedEvaluationInterchange G n).hom.app (CB.mapDerivedCategory.obj M) ≫
        G.mapDerivedCategory.map ((ringedConstantTowerEvaluation B n).hom.app M) =
      (ringedConstantTowerEvaluation A n).hom.app (G.mapDerivedCategory.obj M) := by
  let CA := (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A)
  let CB := (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B)
  let EA := (evaluation ℕᵒᵖ A).obj n
  let EB := (evaluation ℕᵒᵖ B).obj n
  let W := (Functor.whiskeringRight ℕᵒᵖ B A).obj G
  let ρ := (ringedConstantTowerPullback G).inv
  let γ : G.mapDerivedCategory ⟶ G.mapDerivedCategory :=
    Functor.whiskerLeft G.mapDerivedCategory (ringedConstantTowerEvaluation A n).inv ≫
      Functor.whiskerRight ρ EA.mapDerivedCategory ≫
      Functor.whiskerLeft CB.mapDerivedCategory
        (towerDerivedEvaluationInterchange G n).hom ≫
      Functor.whiskerRight (ringedConstantTowerEvaluation B n).hom G.mapDerivedCategory
  suffices hγ : γ = 𝟙 _ by
    have hm := congr_app hγ M
    have hh := congrArg
      (fun z ↦ (ringedConstantTowerEvaluation A n).hom.app
        (G.mapDerivedCategory.obj M) ≫ z) hm
    simpa only [γ, ρ, EA, CB, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, NatTrans.id_app, Functor.id_obj, Functor.comp_obj,
      Category.assoc, Iso.hom_inv_id_app_assoc, Category.comp_id] using hh
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso B (.up ℤ))
  intro I
  let H := (G.mapHomologicalComplex (.up ℤ)).obj I
  let T := (CB.mapHomologicalComplex (.up ℤ)).obj I
  apply (cancel_epi (G.mapDerivedCategoryFactors.inv.app I)).1
  apply (cancel_mono (G.mapDerivedCategoryFactors.hom.app I)).1
  change (G.mapDerivedCategoryFactors.inv.app I ≫
      ((ringedConstantTowerEvaluation A n).inv.app _ ≫
        EA.mapDerivedCategory.map (ρ.app (DerivedCategory.Q.obj I)) ≫
        (towerDerivedEvaluationInterchange G n).hom.app (CB.mapDerivedCategory.obj _) ≫
        G.mapDerivedCategory.map ((ringedConstantTowerEvaluation B n).hom.app _))) ≫
      G.mapDerivedCategoryFactors.hom.app I = _
  simp only [Category.assoc, NatTrans.id_app]
  have hn := (ringedConstantTowerEvaluation A n).inv.naturality
    (G.mapDerivedCategoryFactors.inv.app I)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [reassoc_of% hn]
  erw [← rct_eval_fac B n I, G.mapDerivedCategory.map_comp]
  simp only [Category.assoc]
  erw [← (towerDerivedEvaluationInterchange G n).hom.naturality_assoc
    (CB.mapDerivedCategoryFactors.hom.app I)]
  erw [towerInterchange_fac G n T]
  dsimp only [Functor.comp_map]
  rw [← EA.mapDerivedCategory.map_comp_assoc, ← EA.mapDerivedCategory.map_comp_assoc]
  have hρ : CA.mapDerivedCategory.map (G.mapDerivedCategoryFactors.inv.app I) ≫
      ρ.app (DerivedCategory.Q.obj I) ≫
      W.mapDerivedCategory.map (CB.mapDerivedCategoryFactors.hom.app I) ≫
      W.mapDerivedCategoryFactors.hom.app T =
    CA.mapDerivedCategoryFactors.hom.app H ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ G) (.up ℤ)).hom.app I) := by
    apply (cancel_mono (DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ G) (.up ℤ)).inv.app I))).1
    simp only [Category.assoc]
    erw [← rct_pull_fac G I]
    dsimp only [ρ]
    simp only [Iso.inv_hom_id_app_assoc, ← DerivedCategory.Q.map_comp,
      Iso.hom_inv_id_app]
    erw [← CA.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
      CA.mapDerivedCategory.map_id, Category.id_comp, DerivedCategory.Q.map_id,
      Category.comp_id]
  erw [← EA.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc]
  erw [hρ, EA.mapDerivedCategory.map_comp]
  simp only [Category.assoc]
  erw [EA.mapDerivedCategoryFactors.hom.naturality]
  dsimp only [Functor.comp_map]
  have he : (EA.mapHomologicalComplex (.up ℤ)).map
      ((NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ G) (.up ℤ)).hom.app I) =
      𝟙 H := rfl
  erw [he, CategoryTheory.Functor.map_id, Category.comp_id, rct_eval_fac]
  erw [Category.id_comp, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
  rfl

private theorem pull_projection
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    [Abelian A] [Abelian B] [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wa} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{wb} B] [HasDerivedCategory.{wb} (ℕᵒᵖ ⥤ B)]
    (LA : DiagonalRlim A) (LB : DiagonalRlim B)
    (adjA : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣ LA.R)
    (adjB : (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategory ⊣ LB.R)
    (G : B ⥤ A) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (n : ℕᵒᵖ)
    (pA : LA.R ⟶ ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory)
    (pB : LB.R ⟶ ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory)
    (hA : ∀ K, ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory.map
        (adjA.counit.app K) =
      (ringedConstantTowerEvaluation A n).hom.app (LA.R.obj K) ≫ pA.app K)
    (hB : ∀ K, ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory.map
        (adjB.counit.app K) =
      (ringedConstantTowerEvaluation B n).hom.app (LB.R.obj K) ≫ pB.app K)
    (K : DerivedCategory (ℕᵒᵖ ⥤ B)) :
    let W := (Functor.whiskeringRight ℕᵒᵖ B A).obj G
    let β := (mateEquiv adjB adjA
      (TwoSquare.mk _ _ _ _ (ringedConstantTowerPullback G).inv)).natTrans
    β.app K ≫ pA.app (W.mapDerivedCategory.obj K) ≫
        (towerDerivedEvaluationInterchange G n).hom.app K =
      G.mapDerivedCategory.map (pB.app K) := by
  let CA := (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A)
  let CB := (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B)
  let EA := (evaluation ℕᵒᵖ A).obj n
  let EB := (evaluation ℕᵒᵖ B).obj n
  let W := (Functor.whiskeringRight ℕᵒᵖ B A).obj G
  let ρ := (ringedConstantTowerPullback G).inv
  let β := (mateEquiv adjB adjA (TwoSquare.mk _ _ _ _ ρ)).natTrans
  let e := towerDerivedEvaluationInterchange G n
  let a := ringedConstantTowerEvaluation A n
  let b := ringedConstantTowerEvaluation B n
  have hm := mateEquiv_counit adjB adjA (TwoSquare.mk _ _ _ _ ρ) K
  have he := congrArg (fun q ↦ EA.mapDerivedCategory.map q) hm
  simp only [Functor.map_comp] at he
  change EA.mapDerivedCategory.map (CA.mapDerivedCategory.map (β.app K)) ≫
      EA.mapDerivedCategory.map (adjA.counit.app (W.mapDerivedCategory.obj K)) =
    EA.mapDerivedCategory.map (ρ.app (LB.R.obj K)) ≫
      EA.mapDerivedCategory.map (W.mapDerivedCategory.map (adjB.counit.app K)) at he
  have hA' := hA (W.mapDerivedCategory.obj K)
  change EA.mapDerivedCategory.map (adjA.counit.app (W.mapDerivedCategory.obj K)) =
    a.hom.app (LA.R.obj (W.mapDerivedCategory.obj K)) ≫
      pA.app (W.mapDerivedCategory.obj K) at hA'
  have hB' := hB K
  change EB.mapDerivedCategory.map (adjB.counit.app K) =
    b.hom.app (LB.R.obj K) ≫ pB.app K at hB'
  have hp := pull_evaluation_constant G n (LB.R.obj K)
  change EA.mapDerivedCategory.map (ρ.app (LB.R.obj K)) ≫
      e.hom.app (CB.mapDerivedCategory.obj (LB.R.obj K)) ≫
      G.mapDerivedCategory.map (b.hom.app (LB.R.obj K)) =
    a.hom.app (G.mapDerivedCategory.obj (LB.R.obj K)) at hp
  change β.app K ≫ pA.app (W.mapDerivedCategory.obj K) ≫ e.hom.app K =
    G.mapDerivedCategory.map (pB.app K)
  apply (cancel_epi (a.hom.app (G.mapDerivedCategory.obj (LB.R.obj K)))).1
  calc
    _ = EA.mapDerivedCategory.map (CA.mapDerivedCategory.map (β.app K)) ≫
        a.hom.app (LA.R.obj (W.mapDerivedCategory.obj K)) ≫
          pA.app (W.mapDerivedCategory.obj K) ≫ e.hom.app K := by
      have hn := a.hom.naturality (β.app K)
      change EA.mapDerivedCategory.map (CA.mapDerivedCategory.map (β.app K)) ≫
          a.hom.app (LA.R.obj (W.mapDerivedCategory.obj K)) =
        a.hom.app (G.mapDerivedCategory.obj (LB.R.obj K)) ≫ β.app K at hn
      simpa only [Category.assoc] using congrArg
        (fun z ↦ z ≫ pA.app (W.mapDerivedCategory.obj K) ≫ e.hom.app K) hn.symm
    _ = EA.mapDerivedCategory.map (CA.mapDerivedCategory.map (β.app K)) ≫
        EA.mapDerivedCategory.map (adjA.counit.app (W.mapDerivedCategory.obj K)) ≫
          e.hom.app K := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ EA.mapDerivedCategory.map (CA.mapDerivedCategory.map (β.app K)) ≫
          z ≫ e.hom.app K) hA'.symm
    _ = EA.mapDerivedCategory.map (ρ.app (LB.R.obj K)) ≫
        EA.mapDerivedCategory.map (W.mapDerivedCategory.map (adjB.counit.app K)) ≫
          e.hom.app K := by
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ e.hom.app K) he
    _ = EA.mapDerivedCategory.map (ρ.app (LB.R.obj K)) ≫
        e.hom.app (CB.mapDerivedCategory.obj (LB.R.obj K)) ≫
          G.mapDerivedCategory.map (EB.mapDerivedCategory.map (adjB.counit.app K)) := by
      have hn := e.hom.naturality (adjB.counit.app K)
      change EA.mapDerivedCategory.map (W.mapDerivedCategory.map (adjB.counit.app K)) ≫
          e.hom.app K =
        e.hom.app (CB.mapDerivedCategory.obj (LB.R.obj K)) ≫
          G.mapDerivedCategory.map (EB.mapDerivedCategory.map (adjB.counit.app K)) at hn
      simpa only [Category.assoc] using congrArg
        (fun z ↦ EA.mapDerivedCategory.map (ρ.app (LB.R.obj K)) ≫ z) hn
    _ = EA.mapDerivedCategory.map (ρ.app (LB.R.obj K)) ≫
        e.hom.app (CB.mapDerivedCategory.obj (LB.R.obj K)) ≫
          G.mapDerivedCategory.map (b.hom.app (LB.R.obj K)) ≫
            G.mapDerivedCategory.map (pB.app K) := by
      rw [hB', Functor.map_comp]
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ z ≫ G.mapDerivedCategory.map (pB.app K)) hp

private theorem coneMap_isIso
    {A : Type a} [Category.{va} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wa} (ℕᵒᵖ ⥤ A)]
    (L : DiagonalRlim A) (H : ℕᵒᵖ ⥤ A) (c : Cone H) (hc : IsLimit c)
    [IsIso (diagonalOrdinaryRlim L H)] : IsIso (diagonalTraceConeMap L H c) := by
  have : IsIso (limit.lift H c) :=
    (IsLimit.nonempty_isLimit_iff_isIso_lift (limit.isLimit H)).mp ⟨hc⟩
  dsimp only [diagonalTraceConeMap]
  infer_instance

private theorem pull_single_isIso
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    [Abelian A] [Abelian B] [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wa} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{wb} B] [HasDerivedCategory.{wb} (ℕᵒᵖ ⥤ B)]
    (LA : DiagonalRlim A) (LB : DiagonalRlim B)
    (G : B ⥤ A) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : ℕᵒᵖ ⥤ B)
    (β : LB.R ⋙ G.mapDerivedCategory ⟶
      ((Functor.whiskeringRight ℕᵒᵖ B A).obj G).mapDerivedCategory ⋙ LA.R)
    (hc : G.mapDerivedCategory.map (diagonalTraceConeMap LB H (limit.cone H)) ≫
        β.app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) ≫
        LA.R.map
          ((((Functor.whiskeringRight ℕᵒᵖ B A).obj G).mapDerivedCategorySingleFunctor 0).hom.app H)
          =
      (G.mapDerivedCategorySingleFunctor 0).hom.app (limit H) ≫
        diagonalTraceConeMap LA (H ⋙ G) (G.mapCone (limit.cone H)))
    (hl : IsLimit (G.mapCone (limit.cone H)))
    [IsIso (diagonalOrdinaryRlim LB H)] [IsIso (diagonalOrdinaryRlim LA (H ⋙ G))] :
    IsIso (β.app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)) := by
  have := coneMap_isIso LB H (limit.cone H) (limit.isLimit H)
  have := coneMap_isIso LA (H ⋙ G) (G.mapCone (limit.cone H)) hl
  have : IsIso (G.mapDerivedCategory.map (diagonalTraceConeMap LB H (limit.cone H)) ≫
      β.app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) ≫
        LA.R.map
          ((((Functor.whiskeringRight ℕᵒᵖ B A).obj G).mapDerivedCategorySingleFunctor 0).hom.app H))
      := by
    rw [hc]
    infer_instance
  have := IsIso.of_isIso_comp_left
    (G.mapDerivedCategory.map (diagonalTraceConeMap LB H (limit.cone H)))
    (β.app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) ≫
      LA.R.map
        ((((Functor.whiskeringRight ℕᵒᵖ B A).obj G).mapDerivedCategorySingleFunctor 0).hom.app H))
  exact IsIso.of_isIso_comp_right _
    (LA.R.map
      ((((Functor.whiskeringRight ℕᵒᵖ B A).obj G).mapDerivedCategorySingleFunctor 0).hom.app H))

private theorem exactCone_pull
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wa} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{wb} B] [HasDerivedCategory.{wb} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wd} D]
    (LA : DiagonalRlim A) (LB : DiagonalRlim B)
    (G : B ⥤ A) (U : C ⥤ B) (V : D ⥤ ℕᵒᵖ ⥤ B)
    [G.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (W : (ℕᵒᵖ ⥤ B) ⥤ ℕᵒᵖ ⥤ A)
    [W.Additive] [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (e : G ⋙ Functor.const ℕᵒᵖ ≅ Functor.const ℕᵒᵖ ⋙ W)
    (β : LB.R ⋙ G.mapDerivedCategory ⟶ W.mapDerivedCategory ⋙ LA.R)
    (hc : ∀ (H : ℕᵒᵖ ⥤ B) (c : Cone H),
      G.mapDerivedCategory.map (diagonalTraceConeMap LB H c) ≫
          β.app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) ≫
          LA.R.map ((W.mapDerivedCategorySingleFunctor 0).hom.app H) =
        (G.mapDerivedCategorySingleFunctor 0).hom.app c.pt ≫
          diagonalTraceConeMap LA (W.obj H) ⟨G.obj c.pt, e.hom.app c.pt ≫ W.map c.π⟩)
    (M : C) (N : D) (π : (Functor.const ℕᵒᵖ).obj (U.obj M) ⟶ V.obj N) :
    G.mapDerivedCategory.map (exactConeComparison U V LB M N π) ≫
        β.app (V.mapDerivedCategory.obj ((DerivedCategory.singleFunctor D 0).obj N)) =
      (Functor.mapDerivedCategoryCompIso U G).inv.app
          ((DerivedCategory.singleFunctor C 0).obj M) ≫
        exactConeComparison (U ⋙ G) (V ⋙ W) LA M N
          (e.hom.app (U.obj M) ≫ W.map π) ≫
        LA.R.map ((Functor.mapDerivedCategoryCompIso V W).hom.app
          ((DerivedCategory.singleFunctor D 0).obj N)) := by
  let c : Cone (V.obj N) := ⟨U.obj M, π⟩
  have hn := β.naturality ((V.mapDerivedCategorySingleFunctor 0).inv.app N)
  dsimp only [Functor.comp_map] at hn
  change G.mapDerivedCategory.map
        (LB.R.map ((V.mapDerivedCategorySingleFunctor 0).inv.app N)) ≫
      β.app (V.mapDerivedCategory.obj ((DerivedCategory.singleFunctor D 0).obj N)) =
    β.app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj (V.obj N)) ≫
      LA.R.map (W.mapDerivedCategory.map
        ((V.mapDerivedCategorySingleFunctor 0).inv.app N)) at hn
  have hc' := hc (V.obj N) c
  have hu := Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor U G M
  have hv := Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor V W N
  have hu' : (Functor.mapDerivedCategoryCompIso U G).inv.app
        ((DerivedCategory.singleFunctor (C) 0).obj M) ≫
        ((U ⋙ G).mapDerivedCategorySingleFunctor 0).hom.app M =
      G.mapDerivedCategory.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app (U.obj M) := by
    rw [← hu]
    simp only [Iso.inv_hom_id_app_assoc]
  have hv' : ((V ⋙ W).mapDerivedCategorySingleFunctor 0).inv.app N ≫
        (Functor.mapDerivedCategoryCompIso V W).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj N) =
      (W.mapDerivedCategorySingleFunctor 0).inv.app (V.obj N) ≫
        W.mapDerivedCategory.map ((V.mapDerivedCategorySingleFunctor 0).inv.app N) := by
    apply (cancel_epi (((V ⋙ W).mapDerivedCategorySingleFunctor 0).hom.app N)).1
    rw [Iso.hom_inv_id_app_assoc, ← hv]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← W.mapDerivedCategory.map_comp,
      Iso.hom_inv_id_app]
    erw [W.mapDerivedCategory.map_id, Category.comp_id]
  have hvR := congrArg LA.R.map hv'
  simp only [Functor.map_comp] at hvR
  have hc'' : G.mapDerivedCategory.map (diagonalTraceConeMap LB (V.obj N) c) ≫
        β.app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj (V.obj N)) =
      (G.mapDerivedCategorySingleFunctor 0).hom.app c.pt ≫
        diagonalTraceConeMap LA (W.obj (V.obj N)) ⟨G.obj c.pt, e.hom.app c.pt ≫ W.map c.π⟩ ≫
        LA.R.map ((W.mapDerivedCategorySingleFunctor 0).inv.app (V.obj N)) := by
    apply (cancel_mono (LA.R.map
      ((W.mapDerivedCategorySingleFunctor 0).hom.app (V.obj N)))).1
    simp only [Category.assoc, ← LA.R.map_comp, Iso.inv_hom_id_app]
    erw [LA.R.map_id, Category.comp_id]
    exact hc'
  have hdef : exactConeComparison U V LB M N π =
      (U.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        diagonalTraceConeMap LB (V.obj N) c ≫
        LB.R.map ((V.mapDerivedCategorySingleFunctor 0).inv.app N) := by
    simp only [exactConeComparison, diagonalTraceConeMap, c, Category.assoc]
  rw [hdef]
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]
  rw [reassoc_of% hc'']
  dsimp only [exactConeComparison, diagonalTraceConeMap, c]
  simp only [Category.assoc]
  erw [hvR, reassoc_of% hu']
  rfl

private def completed_push_comparison (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    diagonalTracePush l f ≅ Scheme.proEtaleRingModuleDirectImage f
      (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
      (asIso (diagonalCompletedCoefficientMap l f)) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intros; rfl)))
    (by intros; ext U x; rfl)

/-- The normalized mate on the actual quotient and root towers, its full ordinary cones,
shifted coefficient and root-line arrows, scalar restrictions, and derived morphisms.
Source: blueprint coefficient proof (3).

Proof: extend the full counit normalization from K-injective resolutions to every
complex by naturality. This identifies the ordinary cone map with the transpose
of its strict cone. The mate counit equation and constant/evaluation coherence give
the finite-projection formula. Transpose the two full-cone composites to prove
their equality before evaluation. For each of the two specified endpoint towers,
inverse image preserves its ordinary limiting cone, and the ordinary-to-derived
limit comparisons are invertible by the epimorphic-tower theorem. The full-cone
equation therefore makes the actual mate invertible at those two objects.
Apply the same cone identity to the coefficient-unit and integral root-line cones;
compatibility of the exact localization with single complexes gives their stated
scalar-coordinate equations and hence every requested shift.
For both scalar squares take the inverse mate of the existing direct-image
comparison that is the identity on sections. Its underlying abelian comparison
is invertible by the actual unit equations, so it is a natural isomorphism.
Localize these exact squares canonically. The normalized constant/limit
adjunction commutes with shifts, as does its mate. Naturality is that of the mate
as a natural transformation, for every derived arrow.
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints). -/
theorem diagonalRlim_pullback_endpoints (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : S, Invertible (l : S.residueField y)]
    (LX : DiagonalRlim (DiagonalMod l X)) (LS : DiagonalRlim (DiagonalMod l S))
    (adjX : (Functor.const ℕᵒᵖ : DiagonalMod l X ⥤ DiagonalSystems l X).mapDerivedCategory ⊣ LX.R)
    (adjS : (Functor.const ℕᵒᵖ : DiagonalMod l S ⥤ DiagonalSystems l S).mapDerivedCategory ⊣ LS.R)
    (hCounitX : ∀ (I : CochainComplex (DiagonalSystems l X) ℤ), I.IsKInjective →
      (Functor.const ℕᵒᵖ : DiagonalMod l X ⥤ DiagonalSystems l X).mapDerivedCategory.map
          (LX.η.app I) ≫ adjX.counit.app (DerivedCategory.Q.obj I) =
        (Functor.const ℕᵒᵖ : DiagonalMod l X ⥤
          DiagonalSystems l X).mapDerivedCategoryFactors.hom.app
          (((lim : DiagonalSystems l X ⥤ DiagonalMod l X).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplex (.up ℤ)
            (constLimAdj : (Functor.const ℕᵒᵖ : DiagonalMod l X ⥤ DiagonalSystems l X) ⊣
              lim)).counit.app I))
    (hProjectionX : ∀ (n : ℕ) (K : DerivedCategory (DiagonalSystems l X)),
      ((evaluation ℕᵒᵖ (DiagonalMod l X)).obj (op n)).mapDerivedCategory.map (adjX.counit.app K) =
        (ringedConstantTowerEvaluation (DiagonalMod l X) (op n)).hom.app (LX.R.obj K) ≫
          (LX.projection n).app K)
    (hCounitS : ∀ (I : CochainComplex (DiagonalSystems l S) ℤ), I.IsKInjective →
      (Functor.const ℕᵒᵖ : DiagonalMod l S ⥤ DiagonalSystems l S).mapDerivedCategory.map
          (LS.η.app I) ≫ adjS.counit.app (DerivedCategory.Q.obj I) =
        (Functor.const ℕᵒᵖ : DiagonalMod l S ⥤
          DiagonalSystems l S).mapDerivedCategoryFactors.hom.app
          (((lim : DiagonalSystems l S ⥤ DiagonalMod l S).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplex (.up ℤ)
            (constLimAdj : (Functor.const ℕᵒᵖ : DiagonalMod l S ⥤ DiagonalSystems l S) ⊣
              lim)).counit.app I))
    (hProjectionS : ∀ (n : ℕ) (K : DerivedCategory (DiagonalSystems l S)),
      ((evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n)).mapDerivedCategory.map (adjS.counit.app K) =
        (ringedConstantTowerEvaluation (DiagonalMod l S) (op n)).hom.app (LS.R.obj K) ≫
          (LS.projection n).app K)
    (cS : Chern l (ULift.{u} (Padic l)) S)
    (rS : Restriction l (ULift.{u} (Padic l)) S)
    (aS : Coefficients l (ULift.{u} (Padic l)) S cS rS) :
    (∀ (K : DerivedCategory (DiagonalSystems l S)) (n : ℕ),
      (diagonalRlimPullbackMate l f LX LS adjX adjS).app K ≫
          (LX.projection n).app ((diagonalRlimTowerPull l f).mapDerivedCategory.obj K) ≫
          (diagonalRlimPullbackEvaluation l f n).hom.app K =
        (diagonalRlimPull l f).mapDerivedCategory.map ((LS.projection n).app K)) ∧
    IsIso ((diagonalRlimPullbackMate l f LX LS adjX adjS).app
      ((DerivedCategory.singleFunctor (DiagonalSystems l S) 0).obj
        (rS.F.obj (coefficient S (Arings l (ULift.{u} (Padic l)) S))))) ∧
    IsIso ((diagonalRlimPullbackMate l f LX LS adjX adjS).app
      ((DerivedCategory.singleFunctor (DiagonalSystems l S) 0).obj
        (rS.F.obj (lineModule l (ULift.{u} (Padic l)) cS)))) ∧
    (∀ (H : DiagonalSystems l S) (c : Cone H),
      (diagonalRlimPull l f).mapDerivedCategory.map (diagonalTraceConeMap LS H c) ≫
          (diagonalRlimPullbackMate l f LX LS adjX adjS).app
            ((DerivedCategory.singleFunctor (DiagonalSystems l S) 0).obj H) ≫
          LX.R.map (((diagonalRlimTowerPull l f).mapDerivedCategorySingleFunctor 0).hom.app H) =
        ((diagonalRlimPull l f).mapDerivedCategorySingleFunctor 0).hom.app c.pt ≫
          diagonalTraceConeMap LX ((diagonalRlimTowerPull l f).obj H)
            ((diagonalRlimPull l f).mapCone c)) ∧
    (∀ m : ℤ,
      shiftedComparison
        (diagonalCompletedUnderlying l S ⋙ (diagonalRlimPull l f).mapDerivedCategory)
        (rS.F.mapDerivedCategory ⋙ (diagonalRlimTowerPull l f).mapDerivedCategory ⋙ LX.R)
        ((diagonalRlimPull l f).mapDerivedCategory.map (aS.unitMap l (ULift.{u} (Padic l)) LS) ≫
          (diagonalRlimPullbackMate l f LX LS adjX adjS).app
            (rS.F.mapDerivedCategory.obj (unit S (Arings l (ULift.{u} (Padic l)) S)))) m =
      shiftedComparison
        (diagonalCompletedUnderlying l S ⋙ (diagonalRlimPull l f).mapDerivedCategory)
        (rS.F.mapDerivedCategory ⋙ (diagonalRlimTowerPull l f).mapDerivedCategory ⋙ LX.R)
        (diagonalRlimPulledScalarConeMap l f LX rS
          (SheafOfModules.unit (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)))
          (coefficient S (Arings l (ULift.{u} (Padic l)) S)) aS.coefficientProjection) m) ∧
    (∀ m : ℤ,
      shiftedComparison
        (diagonalCompletedUnderlying l S ⋙ (diagonalRlimPull l f).mapDerivedCategory)
        (rS.F.mapDerivedCategory ⋙ (diagonalRlimTowerPull l f).mapDerivedCategory ⋙ LX.R)
        ((diagonalRlimPull l f).mapDerivedCategory.map (aS.lineMap l (ULift.{u} (Padic l)) LS) ≫
          (diagonalRlimPullbackMate l f LX LS adjX adjS).app
            (rS.F.mapDerivedCategory.obj (line l (ULift.{u} (Padic l)) cS))) m =
      shiftedComparison
        (diagonalCompletedUnderlying l S ⋙ (diagonalRlimPull l f).mapDerivedCategory)
        (rS.F.mapDerivedCategory ⋙ (diagonalRlimTowerPull l f).mapDerivedCategory ⋙ LX.R)
        (diagonalRlimPulledScalarConeMap l f LX rS
          (Scheme.purTwistZlModule S l)
          (lineModule l (ULift.{u} (Padic l)) cS) aS.lineProjection) m) ∧
    (∀ (b : SpTowerShriek.Base l (ULift.{u} (Padic l)))
        (g : SpTowerShriek.Geometry l (ULift.{u} (Padic l)) b f)
        (rX : Restriction l (ULift.{u} (Padic l)) X),
      ∃ (d : g.push ⋙ rS.F ≅ rX.F ⋙ diagonalTraceSystemPush l f)
        (v : rS.F ⋙ diagonalRlimTowerPull l f ≅ g.pull ⋙ rX.F),
        (∀ (M : Systems X (Arings l (ULift.{u} (Padic l)) X)) (n : ℕ)
          (U : S.ProEtᵒᵖ)
          (x : (((g.push ⋙ rS.F).obj M).obj (op n)).obj.obj U),
          HEq (((d.hom.app M).app (op n)).hom.app U x) x) ∧
        (mateEquiv g.ordinaryAdjunction
          ((upperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).whiskerRight ℕᵒᵖ)
          (TwoSquare.mk _ _ _ _ v.hom)).natTrans = d.hom ∧
        NatTrans.CommShift
          (diagonalRlimVaryingSquare l f b g rS rX v).hom ℤ) ∧
    (∃ (d : Scheme.proEtaleRingModuleDirectImage f
          (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
          (asIso (diagonalCompletedCoefficientMap l f)) ⋙ diagonalCompletedRestriction l S ≅
        diagonalCompletedRestriction l X ⋙
          lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
      (v : diagonalCompletedRestriction l S ⋙ diagonalRlimPull l f ≅
        DiagonalCoefficients.diagonalRealizationPull l f ⋙ diagonalCompletedRestriction l X),
      (∀ (M : DiagonalCompleted l X) (U : S.ProEtᵒᵖ)
        (x : ((Scheme.proEtaleRingModuleDirectImage f
          (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
          (asIso (diagonalCompletedCoefficientMap l f)) ⋙
          diagonalCompletedRestriction l S).obj M).obj.obj U),
        HEq ((d.hom.app M).hom.app U x) x) ∧
      (mateEquiv (Scheme.proEtaleRingModuleAdjunction f
          (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
          (asIso (diagonalCompletedCoefficientMap l f)))
        (upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
        (TwoSquare.mk _ _ _ _ v.hom)).natTrans = d.hom ∧
      NatTrans.CommShift (diagonalRlimExactSquare (diagonalCompletedRestriction l S)
        (diagonalRlimPull l f) (DiagonalCoefficients.diagonalRealizationPull l f)
        (diagonalCompletedRestriction l X) v).hom ℤ) ∧
    NatTrans.CommShift (diagonalRlimPullbackMate l f LX LS adjX adjS) ℤ ∧
    (∀ {K K' : DerivedCategory (DiagonalSystems l S)} (z : K ⟶ K'),
      (LS.R ⋙ (diagonalRlimPull l f).mapDerivedCategory).map z ≫
          (diagonalRlimPullbackMate l f LX LS adjX adjS).app K' =
        (diagonalRlimPullbackMate l f LX LS adjX adjS).app K ≫
          ((diagonalRlimTowerPull l f).mapDerivedCategory ⋙ LX.R).map z) := by
  let G := diagonalRlimPull l f
  let W := diagonalRlimTowerPull l f
  let β := diagonalRlimPullbackMate l f LX LS adjX adjS
  have : IsGrothendieckAbelian.{u + 1} (DiagonalMod l X) :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) X
  have : IsGrothendieckAbelian.{u + 1} (DiagonalMod l S) :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) S
  have : IsGrothendieckAbelian.{u + 1} (DiagonalSystems l X) :=
    CategoryTheory.tower_grothendieck (DiagonalMod l X)
  have : IsGrothendieckAbelian.{u + 1} (DiagonalSystems l S) :=
    CategoryTheory.tower_grothendieck (DiagonalMod l S)
  have hX := counit_on_complexes LX adjX hCounitX
  have hS := counit_on_complexes LS adjS hCounitS
  have hCone := pull_cone LX LS adjX adjS
    (cone_transpose LX adjX hX) (cone_transpose LS adjS hS) G
  have hScalar := exactCone_pull LX LS G (diagonalCompletedRestriction l S) rS.F
    W (Functor.compConstIso ℕᵒᵖ G) β (by
      intro H c
      have hπ : (Functor.compConstIso ℕᵒᵖ G).hom.app c.pt ≫ W.map c.π =
          (G.mapCone c).π := by
        apply NatTrans.ext
        funext n
        change (𝟙 (G.obj c.pt)) ≫ G.map (c.π.app n) = G.map (c.π.app n)
        exact Category.id_comp _
      rw [hπ]
      exact hCone H c)
  let := constant_adj_commShift LX adjX hX
  let := constant_adj_commShift LS adjS hS
  have : NatTrans.CommShift (ringedConstantTowerPullback G).inv ℤ := by
    dsimp only [ringedConstantTowerPullback, Iso.trans_inv, Iso.symm_inv]
    infer_instance
  have hShift : NatTrans.CommShift β ℤ :=
    mate_commShift adjS adjX (ringedConstantTowerPullback G).inv
  refine ⟨?_, ?_, ?_, hCone, ?_, ?_, ?_, ?_, hShift, ?_⟩
  · intro K n
    simpa only [diagonalRlimPullbackEvaluation, towerDerivedEvaluationInterchange,
      diagonalRlimPullbackMate, diagonalRlimTowerPull, G,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      eqToIso_refl, Functor.mapDerivedCategoryNatIso_refl, NatTrans.id_app, Category.id_comp]
      using pull_projection LX LS adjX adjS G (op n) (LX.projection n)
        (LS.projection n) (hProjectionX n) (hProjectionS n) K
  · let H := rS.F.obj (coefficient S (Arings l (ULift.{u} (Padic l)) S))
    let := (diagonalRlimTowerLimitPreservation l f cS rS aS).1
    have ht (n : ℕ) : Epi (H.map (homOfLE (Nat.le_succ n)).op) :=
      forgottenTower_epi l S H
        (towerTransitions_of_iso aS.coefficientForget (coefficientTransitions_epi l S)) n
    let := diagonalOrdinaryRlim_isIso_of_epi l S LS H ht
    let := diagonalOrdinaryRlim_isIso_of_epi l X LX (H ⋙ G) (fun n ↦ by
      let := ht n
      exact G.map_epi _)
    exact pull_single_isIso LX LS G H β (hCone H (limit.cone H))
      (isLimitOfPreserves G (limit.isLimit H))
  · let H := rS.F.obj (lineModule l (ULift.{u} (Padic l)) cS)
    let := (diagonalRlimTowerLimitPreservation l f cS rS aS).2
    have hr (n : ℕ) : Epi ((roots l S).map (homOfLE (Nat.le_succ n)).op) := by
      simpa only [roots, Scheme.proEtaleRootsOfUnityTower,
        Functor.ofOpSequence_map_homOfLE_succ] using Scheme.purTwistRootTransitions_epi S l n
    have ht (n : ℕ) : Epi (H.map (homOfLE (Nat.le_succ n)).op) :=
      forgottenTower_epi l S H (towerTransitions_of_iso aS.lineForget hr) n
    let := diagonalOrdinaryRlim_isIso_of_epi l S LS H ht
    let := diagonalOrdinaryRlim_isIso_of_epi l X LX (H ⋙ G) (fun n ↦ by
      let := ht n
      exact G.map_epi _)
    exact pull_single_isIso LX LS G H β (hCone H (limit.cone H))
      (isLimitOfPreserves G (limit.isLimit H))
  · intro m
    exact congrArg (fun t ↦ shiftedComparison
      (diagonalCompletedUnderlying l S ⋙ G.mapDerivedCategory)
      (rS.F.mapDerivedCategory ⋙ W.mapDerivedCategory ⋙ LX.R) t m)
        (hScalar _ _ aS.coefficientProjection)
  · intro m
    exact congrArg (fun t ↦ shiftedComparison
      (diagonalCompletedUnderlying l S ⋙ G.mapDerivedCategory)
      (rS.F.mapDerivedCategory ⋙ W.mapDerivedCategory ⋙ LX.R) t m)
        (hScalar _ _ aS.lineProjection)
  · intro b g rX
    let := g.pullAdditive
    let := g.pullLimits
    let := g.pullColimits
    let := rS.additive
    let := rX.additive
    let := rS.limits
    let := rX.limits
    let := rS.colimits
    let := rX.colimits
    obtain ⟨d, hd⟩ := diagonalTraceVaryingScalarSquare l f b g rS rX
    let am := (upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).whiskerRight ℕᵒᵖ
    let δ := ((mateEquiv g.ordinaryAdjunction am).symm
      (TwoSquare.mk _ _ _ _ d.hom)).natTrans
    let : IsIso δ := diagonalRlimVaryingScalarMate l f b g rS rX d hd
    let v : rS.F ⋙ W ≅ g.pull ⋙ rX.F := asIso δ
    refine ⟨d, v, hd, ?_, ?_⟩
    · change ((mateEquiv g.ordinaryAdjunction am)
        ((mateEquiv g.ordinaryAdjunction am).symm
          (TwoSquare.mk _ _ _ _ d.hom))).natTrans = d.hom
      rw [Equiv.apply_symm_apply]
    · exact exact_square_commShift rS.F W g.pull rX.F v
  · obtain ⟨d₀, hd₀⟩ := diagonalTraceCompletedScalarSquare l f
    let e := completed_push_comparison l f
    let d := Functor.isoWhiskerRight e.symm (diagonalCompletedRestriction l S) ≪≫ d₀
    have hd : ∀ (M : DiagonalCompleted l X) (U : S.ProEtᵒᵖ)
        (x : ((Scheme.proEtaleRingModuleDirectImage f
          (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
          (asIso (diagonalCompletedCoefficientMap l f)) ⋙
          diagonalCompletedRestriction l S).obj M).obj.obj U),
        HEq ((d.hom.app M).hom.app U x) x := by
      intro M U x
      exact hd₀ M U x
    let ar := Scheme.proEtaleRingModuleAdjunction f
      (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
      (asIso (diagonalCompletedCoefficientMap l f))
    let am := upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f
    let δ := ((mateEquiv ar am).symm (TwoSquare.mk _ _ _ _ d.hom)).natTrans
    let : IsIso δ := diagonalRlimCompletedScalarMate l f d hd
    let v : diagonalCompletedRestriction l S ⋙ G ≅
        DiagonalCoefficients.diagonalRealizationPull l f ⋙
          diagonalCompletedRestriction l X := asIso δ
    refine ⟨d, v, hd, ?_, ?_⟩
    · change ((mateEquiv ar am) ((mateEquiv ar am).symm
        (TwoSquare.mk _ _ _ _ d.hom))).natTrans = d.hom
      rw [Equiv.apply_symm_apply]
    · exact exact_square_commShift (diagonalCompletedRestriction l S) G
        (DiagonalCoefficients.diagonalRealizationPull l f)
        (diagonalCompletedRestriction l X) v
  · intro K K' z
    exact β.naturality z

end AlgebraicGeometry.ProEtale.DiagonalTrace
