/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.ClassLimitPresentation.DiagonalClassLimitPresentation
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassReductionPullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalIntegralBoundaryPullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalBaseChangeCartesian
public import WeilConjectures.AlgebraicGeometry.DiagonalReductionPullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalOrdinaryRealizationPullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalCompletedArrowTransport
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalSupportedEndpointTransport
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassComparisonFunctors
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.CategoryTheory.Derived.DerivedTowerCounitProjections
import all WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all WeilConjectures.CategoryTheory.Ringed.RingedConstantTowerPushforwardNormalization

import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalRlimPullbackEndpoints
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceChernTwistExistence
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Coefficient.DiagonalTraceCoefficientRestriction
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Normalized.NormalizedKummerReduction
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernScalarUnit
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarDataExistence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalReducedBoundaryPullback

/-! # The normalized comparison diagram for completed diagonal pullback

Source: blueprint coefficient changes, paragraph (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
open DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor diagonalCompletedSource

/-- The regular module has its canonical pullback endpoint.
Source: blueprint coefficient changes (3), coefficient unit
(blueprint: def-diagonal-class-pullback-frame). -/
def diagonalClassUnitEndpoint
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X S : Scheme.{u}} (f : X ⟶ S) : UnitPullEndpoint R f where
  iso := (Functor.Monoidal.εIso (CondensedRing.upperStar R f)).symm
  normalization := CondensedRing.homEquiv_εIso_inv_hom R f

/-- Realization of the supported completed source, with the exact single comparison.
Source: blueprint coefficient changes (3)
(blueprint: def-diagonal-class-pullback-frame). -/
def diagonalClassRealizedSource (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (e : CompletedRealization l (diagonalSurface Y))
    (s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y) :
    e.F.mapDerivedCategory.obj (diagonalCompletedDomain l Y) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y) :=
  diagonalRealizedSingleSource e.F s

/-- Realization of the completed root line with its degree-two shift.
Source: blueprint coefficient changes (3)
(blueprint: def-diagonal-class-pullback-frame). -/
def diagonalClassRealizedTarget (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (e : CompletedRealization l (diagonalSurface Y)) :
    e.F.mapDerivedCategory.obj (diagonalCompletedCodomain l Y) ≅
      ((DerivedCategory.singleFunctor _ 0).obj (zlLine l (diagonalSurface Y)))⟦(2 : ℤ)⟧ :=
  diagonalRealizedSingleTarget e.F (2 : ℤ) e.lineIso

/-- The integral source endpoint, retaining its exact single normalization.
Source: blueprint coefficient changes (3)
(blueprint: def-diagonal-class-pullback-frame). -/
def diagonalClassIntegralSource {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y'))] :=
  ((upperStar Ab.{u + 1} (baseW g)).mapDerivedCategorySingleFunctor 0).hom.app
      (diagonalIntegralSource Y) ≫
    (DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface Y')) 0).map
      (diagonalBoundarySource (baseW g) (baseP g) (diagonalBaseChange_cartesian g).toCommSq)

/-- The integral units endpoint, retaining its exact degree-one shift.
Source: blueprint coefficient changes (3)
(blueprint: def-diagonal-class-pullback-frame). -/
def diagonalClassIntegralTarget {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y'))] :=
  ((upperStar Ab.{u + 1} (baseW g)).mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj (diagonalComparisonUnits Y)) ≫
    (((upperStar Ab.{u + 1} (baseW g)).mapDerivedCategorySingleFunctor 0).hom.app
      (diagonalComparisonUnits Y) ≫
      (DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface Y')) 0).map
        (diagonalBoundaryUnits (baseW g)))⟦(1 : ℤ)⟧'

/-- Any specified total derived limit admits the full normalized constant/limit
counit once its tower category has K-injective resolutions.

Source: blueprint coefficient changes (3), constant-system derived adjunction.
(blueprint: def-diagonal-class-pullback-frame).

Proof: the universal derived-limit unit is the left Kan universal map. Its Hom
bijection is the hypothesis of the derived tower adjunction theorem. That theorem
constructs the adjunction and its full counit equation on K-injective towers. -/
theorem diagonalClassLimitAdjunction_exists
    (A : Type*) [Category A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{u + 1} A] [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ A)]
    (L : DiagonalRlim A)
    (h : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : M ⟶ I), I.IsKInjective ∧ QuasiIso q) :
    ∃ adj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣ L.R,
      (∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective →
        (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory.map (L.η.app I) ≫
          adj.counit.app (DerivedCategory.Q.obj I) =
        (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplex (.up ℤ) constLimAdj).counit.app I)) ∧
      ∀ (n : ℕ) (K : DerivedCategory (ℕᵒᵖ ⥤ A)),
        ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.map (adj.counit.app K) =
          (ringedConstantTowerEvaluation A (op n)).hom.app (L.R.obj K) ≫
            (L.projection n).app K := by
  let := L.universal
  let := Functor.IsRightDerivedFunctor.isLeftKanExtension L.R L.η
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
  obtain ⟨adj, c, π, hc, hε, hres, hπ, _⟩ :=
    derived_tower_counit_projections.{_, _, u + 1, u + 1, 0, 0} A h L.R L.η
    (fun G ↦ (L.R.homEquivOfIsLeftKanExtension L.η G).bijective) L.computation
  have hc' (n : ℕ) : (c n).hom = (ringedConstantTowerEvaluation A (op n)).hom := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
    intro N
    exact (hc n N).trans (rct_eval_fac A (op n) N)
  have hπI (n : ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (hI : I.IsKInjective) :
      (π n).app (DerivedCategory.Q.obj I) =
        (L.projection n).app (DerivedCategory.Q.obj I) := by
    let := L.computation I hI
    apply (cancel_epi (L.η.app I)).1
    apply (cancel_mono
      (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app I)).1
    have hh := hres n I I (𝟙 I) hI
    simpa using hh.trans (L.normalization I n).symm
  have hπ' (n : ℕ) : π n = L.projection n := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
    intro M
    obtain ⟨I, q, hI, hq⟩ := h M
    let := hq
    apply (cancel_mono
      (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.map
        (DerivedCategory.Q.map q))).1
    rw [← (π n).naturality (DerivedCategory.Q.map q),
      ← (L.projection n).naturality (DerivedCategory.Q.map q), hπI n I hI]
  refine ⟨adj, hε, ?_⟩
  intro n K
  rw [hπ n K, hc' n, hπ' n]

set_option maxHeartbeats 2000000 in
-- Elaborating the full comparison structure checks several derived functor instances.
/-- A comparison frame records actual functors and the full universal normalizations.
It contains neither a completed diagonal arrow nor an equation about such arrows.

Source: blueprint coefficient changes (3), exact scalar, tensor and limit squares.
(blueprint: def-diagonal-class-pullback-frame). -/
structure DiagonalClassPullbackFrame (l : ℕ) [Fact l.Prime]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y')]
    {hY : IsUnit (l : Γ(Y, ⊤))} {hY' : IsUnit (l : Γ(Y', ⊤))}
    {D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y))}
    {D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y'))}
    (d : ClassLimitPresentation l Y hY D) (d' : ClassLimitPresentation l Y' hY' D')
    (e : CompletedRealization l (diagonalSurface Y))
    (e' : CompletedRealization l (diagonalSurface Y')) where
  data : SourcePullback (Profinite.continuousMapRingObj.{u} ℤ_[l]) g (zlLine l)
    (spIntegralComparison (baseP g) l (bottomField l))
    (spIntegralComparison (baseW g) l (bottomField l))
  ordinaryReduction : D.ordinary.E ⋙ diagonalClassTowerPull l (baseW g) ≅
    upperStar Ab.{u + 1} (baseW g) ⋙ D'.ordinary.E
  reduction : D.T ⋙ (diagonalClassTowerPull l (baseW g)).mapDerivedCategory ≅
    (upperStar Ab.{u + 1} (baseW g)).mapDerivedCategory ⋙ D'.T
  reduction_quotients : ∀ (n : ℕ) (M : DiagonalAb (diagonalSurface Y)),
    (diagonalClassPull l (baseW g)).map ((D.ordinary.π n).app M) ≫
        (ordinaryReduction.hom.app M).app (op n) =
      (diagonalClassScalarPullback l (baseW g)).hom.app M ≫
        (D'.ordinary.π n).app ((upperStar Ab.{u + 1} (baseW g)).obj M)
  reduction_computation : ∀ P : CochainComplex (DiagonalAb (diagonalSurface Y)) ℤ,
    (∀ (n : ℕ) (i : ℤ), Mono (l ^ (n + 1) • 𝟙 (P.X i))) →
      (diagonalClassTowerPull l (baseW g)).mapDerivedCategory.map (D.ε.app P) ≫
          (diagonalClassTowerPull l (baseW g)).mapDerivedCategoryFactors.hom.app
            ((D.ordinary.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex ordinaryReduction (.up ℤ)).hom.app P) =
        reduction.hom.app (DerivedCategory.Q.obj P) ≫
          D'.T.map ((upperStar Ab.{u + 1} (baseW g)).mapDerivedCategoryFactors.hom.app P) ≫
          D'.ε.app (((upperStar Ab.{u + 1} (baseW g)).mapHomologicalComplex (.up ℤ)).obj P)
  adj : (Functor.const ℕᵒᵖ : DiagonalMod l (diagonalSurface Y) ⥤
    DiagonalSystems l (diagonalSurface Y)).mapDerivedCategory ⊣ d.L.R
  adj' : (Functor.const ℕᵒᵖ : DiagonalMod l (diagonalSurface Y') ⥤
    DiagonalSystems l (diagonalSurface Y')).mapDerivedCategory ⊣ d'.L.R
  counit : ∀ I : CochainComplex (DiagonalSystems l (diagonalSurface Y)) ℤ,
    I.IsKInjective →
    (Functor.const ℕᵒᵖ : DiagonalMod l (diagonalSurface Y) ⥤
      DiagonalSystems l (diagonalSurface Y)).mapDerivedCategory.map (d.L.η.app I) ≫
        adj.counit.app (DerivedCategory.Q.obj I) =
      (Functor.const ℕᵒᵖ : DiagonalMod l (diagonalSurface Y) ⥤
        DiagonalSystems l (diagonalSurface Y)).mapDerivedCategoryFactors.hom.app
          (((lim : DiagonalSystems l (diagonalSurface Y) ⥤
            DiagonalMod l (diagonalSurface Y)).mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((Adjunction.mapHomologicalComplex (.up ℤ) constLimAdj).counit.app I)
  counit' : ∀ I : CochainComplex (DiagonalSystems l (diagonalSurface Y')) ℤ,
    I.IsKInjective →
    (Functor.const ℕᵒᵖ : DiagonalMod l (diagonalSurface Y') ⥤
      DiagonalSystems l (diagonalSurface Y')).mapDerivedCategory.map (d'.L.η.app I) ≫
        adj'.counit.app (DerivedCategory.Q.obj I) =
      (Functor.const ℕᵒᵖ : DiagonalMod l (diagonalSurface Y') ⥤
        DiagonalSystems l (diagonalSurface Y')).mapDerivedCategoryFactors.hom.app
          (((lim : DiagonalSystems l (diagonalSurface Y') ⥤
            DiagonalMod l (diagonalSurface Y')).mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((Adjunction.mapHomologicalComplex (.up ℤ) constLimAdj).counit.app I)
  projections : ∀ (n : ℕ) (K : DerivedCategory (DiagonalSystems l (diagonalSurface Y))),
    ((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj (op n)).mapDerivedCategory.map
        (adj.counit.app K) =
      (ringedConstantTowerEvaluation (DiagonalMod l (diagonalSurface Y)) (op n)).hom.app
        (d.L.R.obj K) ≫ (d.L.projection n).app K
  projections' : ∀ (n : ℕ) (K : DerivedCategory (DiagonalSystems l (diagonalSurface Y'))),
    ((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y'))).obj (op n)).mapDerivedCategory.map
        (adj'.counit.app K) =
      (ringedConstantTowerEvaluation (DiagonalMod l (diagonalSurface Y')) (op n)).hom.app
        (d'.L.R.obj K) ≫ (d'.L.projection n).app K
  scalarDirect : Scheme.proEtaleRingModuleDirectImage (baseW g)
      (Scheme.purTwistZlCompletion (diagonalSurface Y) l)
      (Scheme.purTwistZlCompletion (diagonalSurface Y') l)
      (asIso (diagonalCompletedCoefficientMap l (baseW g))) ⋙
        diagonalCompletedRestriction l (diagonalSurface Y) ≅
    diagonalCompletedRestriction l (diagonalSurface Y') ⋙
      lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) (baseW g)
  scalar : diagonalCompletedRestriction l (diagonalSurface Y) ⋙
      diagonalClassPull l (baseW g) ≅
    diagonalRealizationPull l (baseW g) ⋙ diagonalCompletedRestriction l (diagonalSurface Y')
  scalar_sections : ∀ (M : DiagonalCompleted l (diagonalSurface Y'))
    (U : (diagonalSurface Y).ProEtᵒᵖ)
    (x : ((Scheme.proEtaleRingModuleDirectImage (baseW g)
      (Scheme.purTwistZlCompletion (diagonalSurface Y) l)
      (Scheme.purTwistZlCompletion (diagonalSurface Y') l)
      (asIso (diagonalCompletedCoefficientMap l (baseW g))) ⋙
      diagonalCompletedRestriction l (diagonalSurface Y)).obj M).obj.obj U),
    HEq ((scalarDirect.hom.app M).hom.app U x) x
  scalar_mate : (mateEquiv (Scheme.proEtaleRingModuleAdjunction (baseW g)
      (Scheme.purTwistZlCompletion (diagonalSurface Y) l)
      (Scheme.purTwistZlCompletion (diagonalSurface Y') l)
      (asIso (diagonalCompletedCoefficientMap l (baseW g))))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) (baseW g))
      (TwoSquare.mk _ _ _ _ scalar.hom)).natTrans = scalarDirect.hom
  pushIso : diagonalTracePush l (baseW g) ≅ Scheme.proEtaleRingModuleDirectImage (baseW g)
    (Scheme.purTwistZlCompletion (diagonalSurface Y) l)
    (Scheme.purTwistZlCompletion (diagonalSurface Y') l)
    (asIso (diagonalCompletedCoefficientMap l (baseW g)))
  push_sections : ∀ (M : DiagonalCompleted l (diagonalSurface Y'))
    (U : (diagonalSurface Y).ProEtᵒᵖ)
    (x : (diagonalTracePush l (baseW g)).obj M |>.val.obj U),
    HEq ((pushIso.hom.app M).val.app U x) x
  ordinarySquare : CompletedOrdinarySquare l (baseW g) e' e
  realization : diagonalRealizationPull l (baseW g) ⋙ e'.F ≅
    e.F ⋙ CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)
  realization_mate : ∀ (M : DiagonalCompleted l (diagonalSurface Y))
    (N : DiagonalCompleted l (diagonalSurface Y'))
    (a : (diagonalRealizationPull l (baseW g)).obj M ⟶ N),
    (CondensedRing.upperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)).homEquiv _ _
        (realization.inv.app M ≫ e'.F.map a) =
      e.F.map ((Scheme.proEtaleRingModuleAdjunction (baseW g)
        (Scheme.purTwistZlCompletion (diagonalSurface Y) l)
        (Scheme.purTwistZlCompletion (diagonalSurface Y') l)
        (asIso (diagonalCompletedCoefficientMap l (baseW g)))).homEquiv _ _ a) ≫
        e.F.map (pushIso.inv.app N) ≫ ordinarySquare.ordinary.hom.app N

open SpTowerClasses

private theorem normalizedChern (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) :
    ∃ c : Chern l (ULift.{u} (Padic l)) T, c.Normalized l (ULift.{u} (Padic l)) := by
  let E := ULift.{u} (Padic l)
  let k := DiagonalTrace.kummerData l T hT
  obtain ⟨r, M, i, a, b, ha, hb⟩ := exists_normalizedKummerReduction l T hT k
  obtain ⟨s⟩ := (WeilConjectures.SemilinearSections.semilinearScalarData.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T)
    (fun n ↦ (Rrings l T).obj (op n))
    (fun n ↦ (Rrings l T).map (homOfLE (Nat.le_succ n)).op)
    (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)
    (SpTowerClasses.coefficientMap l E T)
    (SpTowerClasses.coefficientMap_transition l E T)).1
  obtain ⟨e, he⟩ := exists_normalizedScalarUnit l E T s
  exact ⟨{
    kummer := k
    reduction := r
    rootModule := M
    rootForget := i
    unitIso := a
    rootIso := b
    scalar := s
    scalarUnit := e }, ⟨ha, hb, he⟩⟩

private theorem towerResolutions (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (M : CochainComplex (DiagonalSystems l T) ℤ) :
    ∃ (I : CochainComplex (DiagonalSystems l T) ℤ) (q : M ⟶ I),
      I.IsKInjective ∧ QuasiIso q := by
  let : IsGrothendieckAbelian.{u + 1} (DiagonalMod l T) := inferInstance
  let : IsGrothendieckAbelian.{u + 1} (DiagonalSystems l T) :=
    CategoryTheory.tower_grothendieck (DiagonalMod l T)
  obtain ⟨I, hI, q, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective M
  exact ⟨I, q, hI, hq⟩

private theorem residueUnits (l : ℕ) {T Y : Scheme.{u}} (p : T ⟶ Y)
    (hY : IsUnit (l : Γ(Y, ⊤))) : ∀ x : T, IsUnit (l : T.residueField x) := by
  intro x
  let ψ := (T.residue x).hom.comp
    ((T.presheaf.germ ⊤ x trivial).hom.comp p.appTop.hom)
  simpa only [map_natCast] using hY.map ψ

/-- Construct the normalized comparison frame from its ordinary supported data.
The data field is exactly the supplied one.

Source: blueprint coefficient changes (3), coefficient, scalar and realization comparisons.
(blueprint: def-diagonal-class-pullback-frame).

Proof: the global prime unit induces units in all residue fields of both surfaces.
Construct the normalized Kummer and scalar data, without using the Noetherian
finite-Chern conclusion. Coefficient restriction gives the input to the existing
normalized derived-limit endpoint theorem. Its scalar clause supplies the ordinary
scalar square and mate. K-injective resolutions give normalized constant/limit
adjunctions. Combine those with the proved reduction and ordinary realization
comparisons, retaining the given supported data as a literal field. -/
theorem diagonalClassPullbackFrame_exists (l : ℕ) [Fact l.Prime]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y')]
    {hY : IsUnit (l : Γ(Y, ⊤))} {hY' : IsUnit (l : Γ(Y', ⊤))}
    {D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y))}
    {D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y'))}
    (d : ClassLimitPresentation l Y hY D) (d' : ClassLimitPresentation l Y' hY' D')
    (e : CompletedRealization l (diagonalSurface Y))
    (e' : CompletedRealization l (diagonalSurface Y'))
    (data : SourcePullback (Profinite.continuousMapRingObj.{u} ℤ_[l]) g (zlLine l)
      (spIntegralComparison (baseP g) l (bottomField l))
      (spIntegralComparison (baseW g) l (bottomField l))) :
    ∃ f : DiagonalClassPullbackFrame l g d d' e e', f.data = data := by
  let p : diagonalSurface Y ⟶ Y :=
    pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) ≫ (ProjectiveLine Y ↘ Y)
  let p' : diagonalSurface Y' ⟶ Y' :=
    pullback.fst (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y') ≫ (ProjectiveLine Y' ↘ Y')
  let : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x) :=
    fun x ↦ (residueUnits l p hY x).invertible
  let : ∀ x : diagonalSurface Y', Invertible (l : (diagonalSurface Y').residueField x) :=
    fun x ↦ (residueUnits l p' hY' x).invertible
  obtain ⟨red, q, hred, hq⟩ := diagonalClassReduction_pullback l (baseW g) D D'
  obtain ⟨adj, hc, hp⟩ := diagonalClassLimitAdjunction_exists
    (DiagonalMod l (diagonalSurface Y)) d.L (towerResolutions l (diagonalSurface Y))
  obtain ⟨adj', hc', hp'⟩ := diagonalClassLimitAdjunction_exists
    (DiagonalMod l (diagonalSurface Y')) d'.L (towerResolutions l (diagonalSurface Y'))
  have hW : IsUnit (l : Γ(diagonalSurface Y, ⊤)) := by
    simpa only [map_natCast] using hY.map p.appTop.hom
  obtain ⟨c, hcn⟩ := normalizedChern l (diagonalSurface Y) hW
  obtain ⟨r, ⟨a⟩⟩ := exists_diagonalTraceCoefficientRestriction l (diagonalSurface Y) c hcn
  obtain ⟨_, _, _, _, _, _, _, ⟨scD, sc, hs, hm, _⟩, _⟩ :=
    diagonalRlim_pullback_endpoints l (baseW g) d'.L d.L adj' adj hc' hp' hc hp c r a
  obtain ⟨push, ord, real, hpush, hreal⟩ :=
    diagonalOrdinaryRealization_pullback l (baseW g) e' e
  exact ⟨{
    data := data
    ordinaryReduction := red
    reduction := q
    reduction_quotients := hred
    reduction_computation := hq
    adj := adj
    adj' := adj'
    counit := hc
    counit' := hc'
    projections := hp
    projections' := hp'
    scalarDirect := scD
    scalar := sc
    scalar_sections := hs
    scalar_mate := hm
    pushIso := push
    push_sections := hpush
    ordinarySquare := ord
    realization := real
    realization_mate := hreal }, rfl⟩

/-- The actual mate of the normalized constant/limit adjunctions.
Source: blueprint coefficient changes (3)
(blueprint: def-diagonal-class-pullback-frame). -/
def DiagonalClassPullbackFrame.limitComparison
    (f : DiagonalClassPullbackFrame l g d d' e e') :=
  diagonalClassLimitMate l (baseW g) d'.L d.L f.adj' f.adj

/-- Localization of the normalized completed scalar square.
Source: blueprint coefficient changes (3)
(blueprint: def-diagonal-class-pullback-frame). -/
def DiagonalClassPullbackFrame.scalarComparison
    (f : DiagonalClassPullbackFrame l g d d' e e') :=
  diagonalClassExactSquare (diagonalCompletedRestriction l (diagonalSurface Y))
    (diagonalClassPull l (baseW g)) (diagonalRealizationPull l (baseW g))
    (diagonalCompletedRestriction l (diagonalSurface Y')) f.scalar

section Comparisons
variable {l : ℕ} [Fact l.Prime] {Y Y' : Scheme.{u}} {g : Y' ⟶ Y}
  [DiagonalTraceLocalizations l (diagonalSurface Y)]
  [DiagonalTraceLocalizations l (diagonalSurface Y')]
  {hY : IsUnit (l : Γ(Y, ⊤))} {hY' : IsUnit (l : Γ(Y', ⊤))}
  {D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y))}
  {D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y'))}
  {d : ClassLimitPresentation l Y hY D} {d' : ClassLimitPresentation l Y' hY' D'}
  {e : CompletedRealization l (diagonalSurface Y)}
  {e' : CompletedRealization l (diagonalSurface Y')}

/-- Localization of the normalized realization square, using the published left
inverse image on condensed modules.
Source: blueprint coefficient changes (3)
(blueprint: def-diagonal-class-pullback-frame). -/
def DiagonalClassPullbackFrame.realizationComparison
    (f : DiagonalClassPullbackFrame l g d d' e e') :
    (diagonalRealizationPull l (baseW g)).mapDerivedCategory ⋙ e'.F.mapDerivedCategory ≅
      e.F.mapDerivedCategory ⋙
        derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g) :=
  diagonalClassExactSquare (diagonalRealizationPull l (baseW g)) e'.F e.F
    (CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g))
    f.realization ≪≫
  Functor.isoWhiskerLeft e.F.mapDerivedCategory
    (CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} ℤ_[l])
      (baseW g)).leftDerivedFunctorIsoMapDerivedCategory.symm

/-- The source endpoint of the full reduced integral square.
Source: blueprint coefficient changes (3)
(blueprint: def-diagonal-class-pullback-frame). -/
def DiagonalClassPullbackFrame.systemSource
    (f : DiagonalClassPullbackFrame l g d d' e e') :=
  f.reduction.hom.app ((DerivedCategory.singleFunctor _ 0).obj
    (diagonalIntegralSource Y)) ≫ D'.T.map (diagonalClassIntegralSource g)

/-- The units endpoint of the full reduced integral square.
Source: blueprint coefficient changes (3)
(blueprint: def-diagonal-class-pullback-frame). -/
def DiagonalClassPullbackFrame.systemTarget
    (f : DiagonalClassPullbackFrame l g d d' e e') :=
  f.reduction.hom.app (((DerivedCategory.singleFunctor _ 0).obj
    (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≫ D'.T.map (diagonalClassIntegralTarget g)

/-- The frame carries the entire boundary square, before finite evaluation.
Source: blueprint coefficient changes (3)
(blueprint: def-diagonal-class-pullback-frame).
Proof: apply naturality of reduced positive Cartier pullback to the frame's
reduction comparison. Its endpoints are exactly systemSource and systemTarget. -/
theorem DiagonalClassPullbackFrame.boundary
    (f : DiagonalClassPullbackFrame l g d d' e e') :
    (diagonalClassTowerPull l (baseW g)).mapDerivedCategory.map
        (D.T.map (diagonalIntegralBoundary Y).hom) ≫ f.systemTarget =
      f.systemSource ≫ D'.T.map (diagonalIntegralBoundary Y').hom := by
  exact diagonalReducedBoundary_pullback l g D D' f.reduction.hom

/-- Transport the prescribed condensed supported-source endpoint through the
realization equivalence. This construction uses no completed diagonal arrow.
Source: blueprint coefficient changes (3)
(blueprint: def-diagonal-class-pullback-frame). -/
def DiagonalClassPullbackFrame.sourceComparison
    (f : DiagonalClassPullbackFrame l g d d' e e')
    (s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (s' : e'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y') :
    (diagonalRealizationPull l (baseW g)).mapDerivedCategory.obj
      (diagonalCompletedDomain l Y) ≅ diagonalCompletedDomain l Y' :=
  diagonalSupportedEndpointTransport (Profinite.continuousMapRingObj.{u} ℤ_[l]) g
    (diagonalRealizationPull l (baseW g)).mapDerivedCategory
    e.F.mapDerivedCategory e'.F.mapDerivedCategory f.realizationComparison
    (diagonalClassRealizedSource l Y e s) (diagonalClassRealizedSource l Y' e' s')
    f.data.supported

/-- Transport the prescribed condensed positive-line endpoint and its degree-two
shift through the realization equivalence.
Source: blueprint coefficient changes (3)
(blueprint: def-diagonal-class-pullback-frame). -/
def DiagonalClassPullbackFrame.lineComparison
    (f : DiagonalClassPullbackFrame l g d d' e e') :
    (diagonalRealizationPull l (baseW g)).mapDerivedCategory.obj
      (diagonalCompletedCodomain l Y) ≅ diagonalCompletedCodomain l Y' := by
  have : IsIso f.data.endpoints.lineW.shift := by
    dsimp only [PullEndpoint.shift, PullEndpoint.derived]
    infer_instance
  exact diagonalTransportedEndpoint (diagonalRealizationPull l (baseW g)).mapDerivedCategory
    e.F.mapDerivedCategory e'.F.mapDerivedCategory
    (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g))
    f.realizationComparison (diagonalClassRealizedTarget l Y e)
    (diagonalClassRealizedTarget l Y' e') (asIso f.data.endpoints.lineW.shift)

/-- The closed-source limit endpoint of the normalized comparison diagram.
This is independent of the completed diagonal morphism.
Source: blueprint coefficient changes (3)
(blueprint: def-diagonal-class-pullback-frame). -/
structure DiagonalClassSourceEndpoint
    (s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (s' : e'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y') where
  frame : DiagonalClassPullbackFrame l g d d' e e'
  limit_endpoint : (diagonalClassPull l (baseW g)).mapDerivedCategory.map d.sourceMap ≫
      frame.limitComparison.app
        (D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y))) ≫
      d'.L.R.map frame.systemSource =
    frame.scalarComparison.hom.app (diagonalCompletedDomain l Y) ≫
      (diagonalCompletedUnderlying l (diagonalSurface Y')).map
        (frame.sourceComparison s s').hom ≫ d'.sourceMap

/-- The root-line limit endpoint of the same diagram, including its shift.
This assertion uses only the root tower and the normalized reduction of units.
Source: blueprint coefficient changes (3)
(blueprint: def-diagonal-class-pullback-frame). -/
structure DiagonalClassLineEndpoint
    (frame : DiagonalClassPullbackFrame l g d d' e e') : Prop where
  limit_endpoint : (diagonalClassPull l (baseW g)).mapDerivedCategory.map d.targetMap ≫
      frame.limitComparison.app
        (D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
          (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧)) ≫
      d'.L.R.map frame.systemTarget =
    frame.scalarComparison.hom.app (diagonalCompletedCodomain l Y) ≫
      (diagonalCompletedUnderlying l (diagonalSurface Y')).map
        frame.lineComparison.hom ≫ d'.targetMap

/-- Source realization commutes by the construction of sourceComparison.
Source: blueprint coefficient changes (3)
(blueprint: def-diagonal-class-pullback-frame).
Proof: this is the normalization equation for transport through a fully faithful
realization, with the prescribed single supported-source isomorphism. -/
theorem DiagonalClassSourceEndpoint.realization_endpoint
    {s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y}
    {s' : e'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y'}
    (a : DiagonalClassSourceEndpoint (g := g) (d := d) (d' := d') s s') :
    DiagonalTransportedEndpointMapProperty
      (diagonalRealizationPull l (baseW g)).mapDerivedCategory
      e.F.mapDerivedCategory e'.F.mapDerivedCategory
      (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g))
      a.frame.realizationComparison (diagonalClassRealizedSource l Y e s)
      (DerivedCategory.singleFunctor _ 0) (diagonalClassRealizedSource l Y' e' s')
      (singlePullback (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)
        (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y))
      a.frame.data.supported (a.frame.sourceComparison s s') := by
  exact diagonalSupportedEndpointTransport_normalization
    (Profinite.continuousMapRingObj.{u} ℤ_[l]) g
    (diagonalRealizationPull l (baseW g)).mapDerivedCategory
    e.F.mapDerivedCategory e'.F.mapDerivedCategory a.frame.realizationComparison
    (diagonalClassRealizedSource l Y e s) (diagonalClassRealizedSource l Y' e' s')
    a.frame.data.supported

/-- Line realization commutes by the construction of lineComparison.
Source: blueprint coefficient changes (3)
(blueprint: def-diagonal-class-pullback-frame).
Proof: apply the normalization equation for transport through the realization
with the specified shifted positive-line endpoint. -/
theorem DiagonalClassLineEndpoint.realization_endpoint
    {f : DiagonalClassPullbackFrame l g d d' e e'} (_b : DiagonalClassLineEndpoint f) :
    f.realizationComparison.hom.app (diagonalCompletedCodomain l Y) ≫
      (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)).map
        (diagonalClassRealizedTarget l Y e).hom ≫ f.data.endpoints.lineW.shift =
    e'.F.mapDerivedCategory.map f.lineComparison.hom ≫
      (diagonalClassRealizedTarget l Y' e').hom := by
  have : IsIso f.data.endpoints.lineW.shift := by
    dsimp only [PullEndpoint.shift, PullEndpoint.derived]
    infer_instance
  exact diagonalTransportedEndpoint_normalization _ _ _ _ f.realizationComparison
    (diagonalClassRealizedTarget l Y e) (diagonalClassRealizedTarget l Y' e')
    (asIso f.data.endpoints.lineW.shift)

end Comparisons

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
