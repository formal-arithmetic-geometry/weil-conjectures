/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.CategoryTheory.DerivedMorphismPresheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.IntegralPadicLocalPerfectCriterion
import all WeilConjectures.AlgebraicGeometry.OrdinaryIntegralLocalModels
import all WeilConjectures.AlgebraicGeometry.ExtensionZeroPerfectModelTransport
import all WeilConjectures.AlgebraicGeometry.CompletedTowerPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleTorLocalGlobal
import all WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import all WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
import all WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import all WeilConjectures.AlgebraicGeometry.ProEtaleRingedComparisonInjectiveAcyclicity
import all WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import all WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
import all WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneralSupplement
import all WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModelSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.LeftExact
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlatLimits
import all WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Homology.ShortComplex.Basic
import all Mathlib.CategoryTheory.Subobject.Limits
import all WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.CategoryTheory.RingedSliceExtensionPreservesExact
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import all WeilConjectures.CategoryTheory.RingedSliceExtensionReflectsExact
import all Mathlib.CategoryTheory.Sites.LocallyInjective
import all Mathlib.CategoryTheory.Abelian.Exact
import all WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import all WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import all WeilConjectures.CategoryTheory.LocalizedModuleExactIndependent
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.Algebra.Homology.SliceTensorNatural
import all WeilConjectures.Algebra.Homology.SliceModuleSheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Topology.Sheaves.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.AlgebraicGeometry.DimensionFiniteTypeField
import Mathlib.Algebra.CharP.Invertible
import all WeilConjectures.AlgebraicGeometry.AdicFiniteExchangeEncoding
import all WeilConjectures.AlgebraicGeometry.PerfectChartTensorComparison
import all WeilConjectures.AlgebraicGeometry.IntegralCompletedLocalPerfectCriterion
import all WeilConjectures.AlgebraicGeometry.IntegralResidueFiniteConstants
import WeilConjectures.AlgebraicGeometry.ConstantModelStratificationTransportSupplement

/-! # Finite simultaneous integral perfect charts

Source: Bhatt--Scholze, Proposition 6.6.11, finite covering selection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace AlgebraicGeometry.Scheme
open ProEtale

/-- The actual completed-ring reduction in the equivalent fixed-module presentation.
Index n denotes the positive exponent n+1. Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purIntegralReduction (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (K : PbcCompletedDerived T d) (n : ℕ) :=
  (pbcDerivedFunctionRealization T d n).asEquivalence.inverse.obj
    ((pbcCompletedReduction T d n).obj K)

/-- Termwise reduction of a scalar complex along the specified quotient map.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purScalarReductionComplex {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (n : ℕ) :=
  letI := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).left_adjoint_additive
  ((ModuleCat.extendScalars (Ideal.Quotient.mk (d.ideal ^ (n + 1))) :
    ModuleCat.{u + 1} A ⥤ ModuleCat.{u + 1} (PbcQuotient d n)).mapHomologicalComplex
      (.up ℤ)).obj P

/-- Exact restriction of a reduction to an immersed stratum.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purReductionOnStratum {T Z : Scheme.{u}} (g : Z ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d) (n : ℕ) :=
  ((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} (PbcQuotient d n)) g)
    |>.mapDerivedCategory).obj (purIntegralReduction T d K n)

/-- Exact slice restriction of a derived finite-coefficient complex.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purFixedChart (Z : Scheme.{u}) (B : Type (u + 1)) [CommRing B] (U : Z.ProEt)
    (K : _root_.DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} B))) :
    _root_.DerivedCategory (Sheaf ((ProEt.topology Z).over U) (ModuleCat.{u + 1} B)) :=
  (@CategoryTheory.derivedSliceRestriction.{u} Z.ProEt _
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology Z) B _ U).obj K

/-- A scalar quotient complex realized on the actual localized pro-etale site.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purScalarComplexOnChart (Z : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (U : Z.ProEt)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (n : ℕ) :=
  (DerivedCategory.Q (C := Sheaf ((ProEt.topology Z).over U)
    (ModuleCat.{u + 1} (PbcQuotient d n)))).obj
      (((constantSheaf ((ProEt.topology Z).over U)
        (ModuleCat.{u + 1} (PbcQuotient d n))).mapHomologicalComplex (.up ℤ)).obj
          (purScalarReductionComplex d P n))

private def chartModels {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {T Z : Scheme.{u}}
    (K : PbcCompletedDerived T d) (g : Z ⟶ T) : Prop :=
  ∃ V : Sieve (⊤_ Z.ProEt), V ∈ ProEt.topology Z (⊤_ Z.ProEt) ∧
    ∀ (U : Z.ProEt) (f : U ⟶ ⊤_ Z.ProEt), V f →
      ∃ (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (a b : ℤ),
        P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
        (∀ q : ℤ, Module.Projective A (P.X q) ∧ Module.Finite A (P.X q)) ∧
        Nonempty ((d.pull (U.hom ≫ g)).obj K ≅
          (integralConstantDerived U.left d).obj ((completedConstantQ _).obj P))

private theorem chartModels_pullback {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {T Z W : Scheme.{u}}
    (K : PbcCompletedDerived T d) (g : Z ⟶ T) (h : W ⟶ Z)
    (hm : chartModels d K g) : chartModels d K (h ≫ g) := by
  classical
  obtain ⟨V, hV, hm⟩ := hm
  let F := proEtaleBaseChange h
  let hT := (terminalIsTerminal (C := Z.ProEt)).isTerminalObj F
  let z := hT.from (⊤_ W.ProEt)
  let V' := (V.functorPushforward F).pullback z
  have hV' : V' ∈ ProEt.topology W (⊤_ W.ProEt) :=
    (ProEt.topology W).pullback_stable z
      ((CoverPreserving.of_isContinuous F _ _).cover_preserve hV)
  refine ⟨V', hV', ?_⟩
  intro U f hf
  obtain ⟨B, q, c, hq, _⟩ := hf
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := hm B q hq
  let v : U.left ⟶ B.left := c.left ≫ pullback.fst B.hom h
  have hc : c.left ≫ pullback.snd B.hom h = U.hom := by
    have hw := c.w
    change c.left ≫ pullback.snd B.hom h = U.hom ≫ 𝟙 _ at hw
    simpa only [Category.comp_id] using hw
  have hv : U.hom ≫ (h ≫ g) = v ≫ (B.hom ≫ g) := by
    calc
      _ = (c.left ≫ pullback.snd B.hom h) ≫ (h ≫ g) := by rw [hc]
      _ = v ≫ (B.hom ≫ g) := by
        simpa only [v, Category.assoc] using congrArg
          (fun k ↦ c.left ≫ k ≫ g) (pullback.condition (f := B.hom) (g := h)).symm
  refine ⟨P, a, b, ha, hb, hP, ⟨?_⟩⟩
  exact eqToIso (congrArg (fun k ↦ (d.pull k).obj K) hv) ≪≫
    (d.pullComp v (B.hom ≫ g)).app K ≪≫ (d.pull v).mapIso e ≪≫
      (integralConstantDerivedPullIso d v).app ((completedConstantQ _).obj P)

private theorem common_chart_stratification {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (T : Scheme.{u}) (s : ℕ)
    (K : Fin s → PbcCompletedDerived T d)
    (hK : ∀ j, ∃ S : Stratification T, ∀ r, chartModels d (K j) (S.immersion r)) :
    ∃ S : Stratification T, ∀ r j, chartModels d (K j) (S.immersion r) := by
  induction s with
  | zero =>
    exact ⟨Stratification.trivial T, fun _ j ↦ Fin.elim0 j⟩
  | succ s ih =>
    obtain ⟨S, hS⟩ := ih (fun j ↦ K j.castSucc) (fun j ↦ hK j.castSucc)
    obtain ⟨R, hR⟩ := hK (Fin.last s)
    refine ⟨S.inter R, fun r j ↦ ?_⟩
    induction j using Fin.lastCases with
    | last =>
      simpa only [Stratification.inter_immersion, pullback.condition] using
        chartModels_pullback d (K (Fin.last s))
          (R.immersion (finProdFinEquiv.symm r).2)
          (pullback.snd (S.immersion (finProdFinEquiv.symm r).1)
            (R.immersion (finProdFinEquiv.symm r).2)) (hR _)
    | cast j =>
      exact chartModels_pullback d (K j.castSucc) _ _ (hS _ j)


private theorem finite_precover (X : Scheme.{u}) (W : X.ProEt)
    [CompactSpace W.left] (S : Sieve W) (hS : S ∈ ProEt.topology X W) :
    ∃ (I : Type (u + 1)) (_ : Finite I) (V : I → X.ProEt) (f : ∀ i, V i ⟶ W),
      Presieve.ofArrows V f ∈ (ProEt.precoverage X).coverings W ∧ ∀ i, S (f i) := by
  classical
  have : (ProEt.precoverage X).IsStableUnderComposition := by
    dsimp [ProEt.precoverage]
    infer_instance
  have : (ProEt.precoverage X).HasIsos := by dsimp [ProEt.precoverage]; infer_instance
  have : (ProEt.precoverage X).IsStableUnderBaseChange := by
    dsimp [ProEt.precoverage]
    infer_instance
  obtain ⟨T, hT, hTS⟩ :=
    (ProEt.precoverage X).mem_toGrothendieck_iff_of_isStableUnderComposition.mp hS
  let E := T.preZeroHypercover
  let F := ProEt.forget X ⋙ Over.forget X
  let E' := E.map F
  have hE' : E'.presieve₀ ∈ Scheme.proetalePrecoverage W.left := by
    have he : E'.presieve₀ = Presieve.map F T := by
      dsimp only [E']
      rw [PreZeroHypercover.presieve₀_map]
      exact congrArg (Presieve.map F) T.presieve₀_preZeroHypercover
    rw [he]
    exact hT
  let U : W.left.Cover (Scheme.precoverage @WeaklyEtale) := ⟨E', hE'.2⟩
  let : QuasiCompactCover U.toPreZeroHypercover :=
    Scheme.presieve₀_mem_qcPrecoverage_iff.mp hE'.1
  obtain ⟨A, hfin, hqc, ⟨r⟩⟩ := ProEt.exists_finite_refinement W.left U
  let := hfin
  let := hqc
  have (i : A.I₀) : WeaklyEtale (A.f i) := A.map_prop i
  let V : A.I₀ → X.ProEt := fun i ↦ ProEt.mk (A.f i ≫ W.hom)
  let f : ∀ i, V i ⟶ W := fun i ↦ MorphismProperty.Over.homMk (A.f i) (by rfl)
  refine ⟨A.I₀, hfin, V, f, ?_, ?_⟩
  · change Presieve.map F (Presieve.ofArrows V f) ∈ Scheme.proetalePrecoverage W.left
    rw [Presieve.map_ofArrows]
    change A.presieve₀ ∈ Scheme.proetalePrecoverage W.left
    exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr hqc, A.mem₀⟩
  · intro i
    let e := r.s₀ i
    let g : V i ⟶ E.X e := MorphismProperty.Over.homMk (r.h₀ i) (by
      change r.h₀ i ≫ (E.X e).hom = A.f i ≫ W.hom
      have he : r.h₀ i ≫ (E.f e).left = A.f i := r.w₀ i
      rw [← he, Category.assoc]
      congr 1
      simp)
    have hg : g ≫ E.f e = f i := by
      apply (ProEt.forget X).map_injective
      apply Over.OverMorphism.ext
      exact r.w₀ i
    rw [← hg]
    exact S.downward_closed (hTS _ _ e.2) g

private theorem padic_chart_stratification
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    (hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n) (hl : IsUnit (l : Γ(T, ⊤)))
    (K : PbcCompletedDerived T (pbcPadicCoefficientDatum l E))
    (hK : IsPbcBoundedConstructibleComplete T l E K) :
    ∃ S : Stratification T, ∀ r, chartModels (pbcPadicCoefficientDatum l E) K
      (S.immersion r) := by
  obtain ⟨S, hS⟩ := (integralPadicLocalPerfectCriterion T l E hdim hl K).mp hK
  let R := S.withConstructibleStrata
    (fun r ↦ (S.isLocallyClosed_stratum r).isConstructible_of_noetherianSpace)
  refine ⟨R, fun r ↦ ?_⟩
  obtain ⟨V, hV, hm⟩ := hS r
  refine ⟨V, hV, fun U f hf ↦ ?_⟩
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := hm U f hf
  refine ⟨P, a, b, ha, hb, hP, ⟨?_⟩⟩
  exact (pullbackDatumOrdinaryTransport (U.hom ≫ S.immersion r)
    (pbcPadicCoefficientDatum l E)).app K |>.symm.trans e

private theorem finite_chart_models {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {T Z : Scheme.{u}} [CompactSpace Z]
    (K : PbcCompletedDerived T d) (g : Z ⟶ T) (hm : chartModels d K g) :
    ∃ (m : ℕ) (U : Fin m → Z.ProEt)
      (f : ∀ c, U c ⟶ ProEt.mk (𝟙 Z))
      (P : Fin m → CochainComplex (ModuleCat.{u + 1} A) ℤ)
      (a b : Fin m → ℤ),
      Presieve.ofArrows U f ∈ (ProEt.precoverage Z).coverings _ ∧
      ∀ c, (P c).IsStrictlyGE (a c) ∧ (P c).IsStrictlyLE (b c) ∧
        (∀ q, Module.Projective A ((P c).X q) ∧ Module.Finite A ((P c).X q)) ∧
        Nonempty ((d.pull ((U c).hom ≫ g)).obj K ≅
          (integralConstantDerived (U c).left d).obj ((completedConstantQ _).obj (P c))) := by
  classical
  obtain ⟨V, hV, hm⟩ := hm
  let z := (terminalIsTerminal (C := Z.ProEt)).from (ProEt.mk (𝟙 Z))
  have hv := (ProEt.topology Z).pullback_stable z hV
  have : CompactSpace (ProEt.mk (𝟙 Z)).left := ‹CompactSpace Z›
  obtain ⟨I, hI, U, f, hf, hi⟩ := finite_precover Z (ProEt.mk (𝟙 Z)) _ hv
  have := hI
  let := Fintype.ofFinite I
  let e := Fintype.equivFin I
  have hc : ∀ i, ∃ P a b, P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ q, Module.Projective A (P.X q) ∧ Module.Finite A (P.X q)) ∧
      Nonempty ((d.pull ((U i).hom ≫ g)).obj K ≅
        (integralConstantDerived (U i).left d).obj ((completedConstantQ _).obj P)) :=
    fun i ↦ hm (U i) (f i ≫ z) (hi i)
  choose P a b hp using hc
  refine ⟨Fintype.card I, U ∘ e.symm, fun c ↦ f (e.symm c),
    P ∘ e.symm, a ∘ e.symm, b ∘ e.symm, ?_, fun c ↦ hp (e.symm c)⟩
  rw [Presieve.ofArrows_comp_eq_of_surjective f e.symm.surjective]
  exact hf

private theorem positive_chart_stratification {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (T : Scheme.{u}) (s : ℕ)
    (K : Fin s → PbcCompletedDerived T d)
    (hK : ∃ S : Stratification T, ∀ r j, chartModels d (K j) (S.immersion r)) :
    ∃ S : Stratification T, 0 < S.n ∧ ∀ r j, chartModels d (K j) (S.immersion r) := by
  classical
  obtain ⟨S, hS⟩ := hK
  by_cases hn : S.n = 0
  · have : IsEmpty T := ⟨fun x ↦ by
      have hx : x ∈ ⋃ i, S.stratum i := by rw [S.iUnion_stratum_eq_univ]; trivial
      obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
      exact (Fin.elim0 (hn ▸ i))⟩
    refine ⟨Stratification.trivial T, by exact Nat.zero_lt_one, fun r j ↦ ?_⟩
    have : IsEmpty ((Stratification.trivial T).domain r) := ‹IsEmpty T›
    have : IsEmpty (⊤_ ((Stratification.trivial T).domain r).ProEt).left :=
      (⊤_ ((Stratification.trivial T).domain r).ProEt).hom.base.1.1.isEmpty (β := T)
    exact ⟨⊥, ProEt.bot_mem_topology _, fun _ _ h ↦ False.elim h⟩
  · exact ⟨S, Nat.pos_of_ne_zero hn, hS⟩

private theorem zero_chart_model {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {T Z : Scheme.{u}}
    (K : PbcCompletedDerived T d) (g : Z ⟶ T) (hK : IsZero K) (U : Z.ProEt) :
    Nonempty ((d.pull (U.hom ≫ g)).obj K ≅
      (integralConstantDerived U.left d).obj
        ((completedConstantQ _).obj (0 : CochainComplex (ModuleCat.{u + 1} A) ℤ))) := by
  let := (integralConstantModule_exact U.left d).1
  let := (integralConstantModule_exact U.left d).2
  change IsZero K at hK
  change Nonempty (_ ≅ _)
  have : (integralConstantModule U.left d).mapDerivedCategory.PreservesZeroMorphisms :=
    inferInstance
  exact ⟨((d.pull _).map_isZero hK).iso
    ((integralConstantModule U.left d).mapDerivedCategory.map_isZero
      ((completedConstantQ _).map_isZero (isZero_zero _)))⟩

private def reduction_pull_iso {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {X Y : Scheme.{u}} (h : X ⟶ Y)
    (K : PbcCompletedDerived Y d) (n : ℕ) :
    ((ProEtale.upperStar (ModuleCat.{u + 1} (PbcQuotient d n)) h)
      |>.mapDerivedCategory).obj (purIntegralReduction Y d K n) ≅
        purIntegralReduction X d ((d.pull h).obj K) n := by
  let FY := (pbcDerivedFunctionRealization Y d n).asEquivalence
  let FX := (pbcDerivedFunctionRealization X d n).asEquivalence
  let H := ProEtale.upperStar (ModuleCat.{u + 1} (PbcQuotient d n)) h
  let e := Functor.mapDerivedCategoryNatIso
    (WeilConjectures.finitePullbackCoordinates h d n).choose ≪≫
      Functor.mapDerivedCategoryCompIso _ _
  let q : H.mapDerivedCategory ⋙ FX.functor ≅
      FY.functor ⋙ d.finitePull h n :=
    (Functor.mapDerivedCategoryCompIso H (pbcFunctionRealization X d n)).symm ≪≫ e
  apply FX.functor.preimageIso
  exact (q.app (FY.inverse.obj ((d.reduction Y n).obj K))) ≪≫
    (d.finitePull h n).mapIso (FY.counitIso.app _) ≪≫
    (d.chi h n).app K ≪≫ (FX.counitIso.app _).symm

private def finite_constant_realization (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} (PbcQuotient d n)) ⋙
      pbcFunctionRealization X d n ⋙ pbcRestrict (pbcLevelConstantComparison X d n).hom ≅
        adicLisseConstantModules X (PbcQuotient d n) := by
  let B := PbcQuotient d n
  let R := (adicLisseForget X).obj (adicLisseConstantRing X B)
  let S := (adicLisseForget X).obj (d.finiteRing X n)
  let j := (adicLisseForget X).mapIso (pbcLevelConstantComparison X d n)
  let α := Functor.whiskerRight (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have : Presheaf.IsLocallyInjective (ProEt.topology X) α := by
    exact adicLisseConstantUnit_locallyInjective X B
  have : Presheaf.IsLocallySurjective (ProEt.topology X) α := by
    exact adicLisseConstantUnit_locallySurjective X B
  have hα : α ≫ j.hom.hom =
      (Functor.const X.ProEtᵒᵖ).map (RingCat.ofHom (RingHom.id B)) ≫
        pbcFunctionScalars X d n := by
    rw [WeilConjectures.finiteScalars_constantUnit]
    simp only [RingCat.ofHom_id]
    rfl
  let t := (pbcAssociatedRestriction_exists X B B R S α
    (pbcFunctionScalars X d n) (RingHom.id B) j.hom hα).exists.choose
  let t' : pbcAssociatedModule X B R α ≅
      pbcFunctionRealization X d n ⋙ pbcRestrict (pbcLevelConstantComparison X d n).hom :=
    t
  exact Functor.isoWhiskerLeft _ t'.symm ≪≫ associatedConstants X B R α

private def reduction_constant_iso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (b : ℤ) (hb : P.IsStrictlyLE b)
    (hP : ∀ q, Module.Projective A (P.X q)) (n : ℕ) :
    purIntegralReduction X d
      ((integralConstantDerived X d).obj ((completedConstantQ _).obj P)) n ≅
      DerivedCategory.Q.obj
        (((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} (PbcQuotient d n)))
          |>.mapHomologicalComplex (.up ℤ)).obj (purScalarReductionComplex d P n)) := by
  let := hb
  let c := CompletedConstantReduction.base X d.ideal ≫ (pbcCompletedComparison X d).hom
  let p := pbcAdicProjection X d n
  let j := pbcLevelConstantComparison X d n
  let q := Ideal.Quotient.mk (d.ideal ^ (n + 1))
  let β := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom q)
  have hcp : c ≫ p = β ≫ j.hom := by
    dsimp [c, p, pbcAdicProjection, pbcCompletedComparison]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc]
    have h := (CompletedConstantReduction.base_exists X d.ideal).choose_spec.1 n
    change CompletedConstantReduction.base X d.ideal ≫ _ = _ at h
    rw [h]
    rfl
  have hcpj : c ≫ p ≫ j.inv = β := by
    rw [← Category.assoc, hcp, Category.assoc, j.hom_inv_id, Category.comp_id]
  let C₀ := DerivedCategory.Q.obj ((CompletedConstantReduction.constantComplex X A).obj P)
  have heP : (integralConstantDerived X d).obj ((completedConstantQ _).obj P) ≅
      (pbcDerivedExtend c).obj C₀ := by
    let F := adicLisseConstantModules X A
    have : F.Additive := CompletedConstantReduction.constant_additive X A
    have : PreservesFiniteLimits F := (CompletedConstantReduction.constant_exact X A).1
    have : PreservesFiniteColimits F := (CompletedConstantReduction.constant_exact X A).2
    let C := (CompletedConstantReduction.constantComplex X A).obj P
    have : IsIso (pbcComplexCounit c C) := by
      have := pbcExtensionCounit_isIso c C (constant_kflat X P b hP)
      dsimp only [pbcComplexCounit]
      infer_instance
    exact (integralRealizationFactors X d).app P ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
        (ordinaryConstantModel X d) (.up ℤ)).app P) ≪≫
      (DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (F ⋙ pbcExtend c)) (.up ℤ)).app P)).symm ≪≫
      (asIso (pbcComplexCounit c C)).symm
  let L := (pbcCompletedReduction X d n).obj
    ((integralConstantDerived X d).obj ((completedConstantQ _).obj P))
  let Rj := pbcDerivedRestrict j.hom
  have : Rj.IsEquivalence := derivedRestrictIso_isEquivalence j
  let eglobal : Rj.obj L ≅ DerivedCategory.Q.obj
      ((CompletedConstantReduction.constantComplex X (PbcQuotient d n)).obj
        (purScalarReductionComplex d P n)) :=
    Rj.mapIso ((pbcDerivedExtend p).mapIso heP) ≪≫
      (restrictIsoAsExtend j).app _ ≪≫
      (pbcDerivedExtend j.inv).mapIso (pbcReductionNormalization c p (c ≫ p) rfl C₀) ≪≫
      pbcReductionNormalization (c ≫ p) j.inv β hcpj C₀ ≪≫
      constantTensorIso X q P b hP
  let FY := (pbcDerivedFunctionRealization X d n).asEquivalence
  let C := constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} (PbcQuotient d n))
  let D := purScalarReductionComplex d P n
  let F := adicLisseConstantModules X (PbcQuotient d n)
  have : F.Additive := CompletedConstantReduction.constant_additive X _
  have := (CompletedConstantReduction.constant_exact X (PbcQuotient d n)).1
  have := (CompletedConstantReduction.constant_exact X (PbcQuotient d n)).2
  let t : FY.functor ⋙ Rj ≅ (pbcFunctionRealization X d n ⋙
      pbcRestrict j.hom).mapDerivedCategory := (Functor.mapDerivedCategoryCompIso _ _).symm
  let t' : C.mapDerivedCategory ⋙ FY.functor ⋙ Rj ≅ F.mapDerivedCategory :=
    Functor.isoWhiskerLeft C.mapDerivedCategory t ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (finite_constant_realization X d n)
  apply FY.functor.preimageIso
  apply Rj.preimageIso
  exact Rj.mapIso (FY.counitIso.app L) ≪≫ eglobal ≪≫
    (F.mapDerivedCategoryFactors.app D).symm ≪≫
    (t'.app (DerivedCategory.Q.obj D)).symm ≪≫
    Rj.mapIso (FY.functor.mapIso (C.mapDerivedCategoryFactors.app D))

private theorem chart_reduction {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {T Z : Scheme.{u}} (g : Z ⟶ T)
    (K : PbcCompletedDerived T d) (U : Z.ProEt)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (b : ℤ) (hb : P.IsStrictlyLE b)
    (hP : ∀ q, Module.Projective A (P.X q))
    (e : Nonempty ((d.pull (U.hom ≫ g)).obj K ≅
      (integralConstantDerived U.left d).obj ((completedConstantQ _).obj P))) (n : ℕ) :
    Nonempty (purFixedChart Z (PbcQuotient d n) U
      (purReductionOnStratum g d K n) ≅ purScalarComplexOnChart Z d U P n) := by
  let B := PbcQuotient d n
  have := ProEt.sliceDense Z U
  let E := (ProEt.sliceEquiv Z U).sheafCongr
    ((ProEt.topology Z).over U) (ProEt.topology U.left) (ModuleCat.{u + 1} B)
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : E.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let ED := E.mapDerivedCategory
  let G := (ProEt.topology Z).overPullback (ModuleCat.{u + 1} B) U
  let H := ProEtale.upperStar (ModuleCat.{u + 1} B) U.hom
  let er : G ⋙ E.functor ≅ H :=
    (NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _
      (NatIso.ofComponents (fun _ ↦ Iso.refl _))) ≪≫
      (ProEtale.upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} B) U.hom U.prop).symm)
  let r : G.mapDerivedCategory ⋙ ED.functor ≅ H.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso er
  let C := constantSheaf ((ProEt.topology Z).over U) (ModuleCat.{u + 1} B)
  let C' := constantSheaf (ProEt.topology U.left) (ModuleCat.{u + 1} B)
  let ec := (ProEt.sliceEquiv Z U).constantSheafSheafCongrIso
    ((ProEt.topology Z).over U) (ProEt.topology U.left)
    (ModuleCat.{u + 1} B) (Over.mkIdTerminal (X := U))
  let cr : C.mapDerivedCategory ⋙ ED.functor ≅ C'.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso ec
  let D := purScalarReductionComplex d P n
  let e' : H.mapDerivedCategory.obj (purReductionOnStratum g d K n) ≅
      DerivedCategory.Q.obj ((C'.mapHomologicalComplex (.up ℤ)).obj D) :=
    H.mapDerivedCategory.mapIso (reduction_pull_iso d g K n) ≪≫
      reduction_pull_iso d U.hom ((d.pull g).obj K) n ≪≫
      (pbcDerivedFunctionRealization U.left d n).asEquivalence.inverse.mapIso
        ((d.reduction U.left n).mapIso
          (((d.pullComp U.hom g).app K).symm ≪≫ e.some)) ≪≫
      reduction_constant_iso U.left d P b hb hP n
  exact ⟨ED.functor.preimageIso
    (r.app _ ≪≫ e' ≪≫ (C'.mapDerivedCategoryFactors.app D).symm ≪≫
      (cr.app (DerivedCategory.Q.obj D)).symm ≪≫
      ED.functor.mapIso (C.mapDerivedCategoryFactors.app D))⟩

/-- Simultaneous finite perfect charts, chosen before any reduction index.
Source: Bhatt--Scholze, Proposition 6.6.11 and Lemma 6.6.10(1)
(blueprint: lem-pur-integral-finite-perfect-charts).

Proof: apply the actual-valuation-ring local perfect criterion to each family member.
Intersect their finite stratifications by scheme fibre products. Pull back each local
cover and its perfect scalar model through the refinement projections; the normalized
completed-coefficient inverse-image comparison and tensor associativity preserve these
models. Each stratum is Noetherian and quasi-compact, so choose a finite subcover by
quasi-compact pieces, retaining the original scalar model on each selected piece.
Take the minimum of all lower term bounds and the maximum of all upper term bounds,
including zero among both finite sets, to obtain one ordered interval. Restriction
preserves zero terms, so every retained representative has that interval.
The perfect-chart tensor comparison computes all actual reductions by the termwise
quotients on those same charts. For an all-zero family take zero
complexes, the identity stratification, identity charts and [0,0]. For an empty family
the charts are vacuous and the same stratification and interval apply; on the empty
scheme these choices are valid as well. No Tor or etale-origin conclusion is assumed. -/
theorem pur_integral_finite_perfect_charts
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpl : p ≠ l)
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    (s : ℕ) (K : Fin s → PbcCompletedDerived T (pbcPadicCoefficientDatum l E))
    (_hK : ∀ j : Fin s,
      IsPbcBoundedConstructibleComplete T l E (K j)) :
    ∃ a b : ℤ, a ≤ b ∧
      ((∀ j : Fin s, IsZero (K j)) → a = 0 ∧ b = 0) ∧
      ∃ S : Stratification T, 0 < S.n ∧
        (∀ (r : Fin S.n) (j : Fin s),
          ∃ (m : ℕ) (U : Fin m → (S.domain r).ProEt)
            (f : ∀ c : Fin m, U c ⟶ ProEt.mk (𝟙 (S.domain r)))
            (P : Fin m → CochainComplex
              (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ),
            Presieve.ofArrows U f ∈ (ProEt.precoverage (S.domain r)).coverings _ ∧
            ∀ c : Fin m,
              ((P c).IsStrictlyGE a ∧ (P c).IsStrictlyLE b) ∧
              (∀ q : ℤ, Module.Projective (Padic.coefficientExtensionIntegers l E)
                ((P c).X q) ∧ Module.Finite (Padic.coefficientExtensionIntegers l E)
                  ((P c).X q)) ∧
              Nonempty (integralLocalDerived (S.immersion r)
                (pbcAdicCompletion T (pbcPadicCoefficientDatum l E)) (U c) (K j) ≅
                integralLocalDerived (S.immersion r)
                  (pbcAdicCompletion T (pbcPadicCoefficientDatum l E)) (U c)
                  ((integralConstantDerived T (pbcPadicCoefficientDatum l E)).obj
                    ((completedConstantQ _).obj (P c)))) ∧
              ∀ n : ℕ,
                Nonempty (purFixedChart (S.domain r)
                  (PbcQuotient (pbcPadicCoefficientDatum l E) n) (U c)
                  (purReductionOnStratum (S.immersion r)
                    (pbcPadicCoefficientDatum l E) (K j) n) ≅
                  purScalarComplexOnChart (S.domain r) (pbcPadicCoefficientDatum l E)
                    (U c) (P c) n)) := by
  classical
  let d := pbcPadicCoefficientDatum l E
  by_cases hz : ∀ j : Fin s, IsZero (K j)
  · refine ⟨0, 0, le_rfl, fun _ ↦ ⟨rfl, rfl⟩,
      Stratification.trivial T, Nat.zero_lt_one, fun r j ↦ ?_⟩
    let Z := (Stratification.trivial T).domain r
    let U : Z.ProEt := ProEt.mk (𝟙 Z)
    let P : CochainComplex
        (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ := 0
    have hP (q : ℤ) : Module.Projective (Padic.coefficientExtensionIntegers l E) (P.X q) ∧
        Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X q) := by
      have : Subsingleton (P.X q) := ModuleCat.subsingleton_of_isZero
        ((HomologicalComplex.eval _ _ q).map_isZero (isZero_zero _))
      exact ⟨inferInstance, inferInstance⟩
    have he := zero_chart_model d (K j) ((Stratification.trivial T).immersion r) (hz j) U
    refine ⟨1, fun _ ↦ U, fun _ ↦ 𝟙 U, fun _ ↦ P, ?_, fun _ ↦ ?_⟩
    · have : (ProEt.precoverage Z).HasIsos := by
        dsimp [ProEt.precoverage]
        infer_instance
      rw [Presieve.ofArrows_of_unique]
      exact Precoverage.mem_coverings_of_isIso _
    · exact ⟨⟨inferInstance, inferInstance⟩, hP,
        (localModel_iff d _ U (K j) ((completedConstantQ _).obj P)).mpr he,
        fun n ↦ chart_reduction d _ (K j) U P 0 inferInstance (fun q ↦ (hP q).1) he n⟩
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of k))
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian
    (T ↘ Spec (.of k))
  have : IsNoetherian T := ⟨⟩
  have hdim := exists_topologicalKrullDim_le (T ↘ Spec (.of k))
  have hlk : IsUnit (l : k) := (CharP.isUnit_natCast_iff (Fact.out : p.Prime)).2
    (fun h ↦ _hpl ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
      (Fact.out : l.Prime)).mp h))
  have hl : IsUnit (l : Γ(T, ⊤)) := by
    let f := (T ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
    simpa using hlk.map f
  obtain ⟨S, hSn, hS⟩ := positive_chart_stratification d T s K
    (common_chart_stratification d T s K
      (fun j ↦ padic_chart_stratification l E T hdim hl (K j) (_hK j)))
  have (r : Fin S.n) : TopologicalSpace.NoetherianSpace (S.domain r) :=
    (S.immersion r).isEmbedding.isInducing.noetherianSpace
  have hfin := fun r j ↦ finite_chart_models d (K j) (S.immersion r) (hS r j)
  choose m U f P lo hi hc hp using hfin
  let I := Σ r : Fin S.n, Σ j : Fin s, Fin (m r j)
  obtain ⟨a, ha0, ha⟩ := (Finite.bddBelow_range
    (fun i : I ↦ lo i.1 i.2.1 i.2.2)).exists_le (0 : ℤ)
  obtain ⟨b, hb0, hb⟩ := (Finite.bddAbove_range
    (fun i : I ↦ hi i.1 i.2.1 i.2.2)).exists_ge (0 : ℤ)
  refine ⟨a, b, ha0.trans hb0, fun h ↦ (hz h).elim, S, hSn, fun r j ↦
    ⟨m r j, U r j, f r j, P r j, hc r j, fun c ↦ ?_⟩⟩
  obtain ⟨hlo, hhi, hP, he⟩ := hp r j c
  have := hlo
  have := hhi
  refine ⟨⟨(P r j c).isStrictlyGE_of_ge a (lo r j c)
    (ha _ ⟨⟨r, j, c⟩, rfl⟩), (P r j c).isStrictlyLE_of_le (hi r j c) b
    (hb _ ⟨⟨r, j, c⟩, rfl⟩)⟩, hP, ?_, ?_⟩
  · exact (localModel_iff d (S.immersion r) (U r j c) (K j)
      ((completedConstantQ _).obj (P r j c))).mpr he
  · exact fun n ↦ chart_reduction d (S.immersion r) (K j) (U r j c)
      (P r j c) (hi r j c) hhi (fun q ↦ (hP q).1) he n

end AlgebraicGeometry.Scheme
