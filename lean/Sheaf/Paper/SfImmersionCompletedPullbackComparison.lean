/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Sheaf.Paper.PbcActualStrictPullback
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
public import Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison
public import Sheaf.Paper.SfImmersionCompletedPullbackCoreA
import all Sheaf.Paper.SfImmersionCompletedPullbackCoreA
import Sheaf.Paper.SfImmersionFiniteReductionInterval
import all Sheaf.Paper.CompletedTowerPullback
import Sheaf.Paper.IntegralCoefficientCompletenessTransport
import Sheaf.Paper.PbcIntrinsicTowerComplete
import all Sheaf.Paper.PbcCompletedPullbackActual

import Sheaf.Paper.CompletedOpenExchangeTransport
import Sheaf.CategoryTheory.StrictRoosModel
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import all Sheaf.Paper.SfImmersionFiniteNormalization
import all Sheaf.Paper.SfImmersionRoosNormalization
import all Sheaf.Paper.WeilTensorProduct
import all Sheaf.Paper.AdicCoefficientDatum
import all Sheaf.CategoryTheory.ExactAdjointTowerModels

/-! # Ordinary immersion pullback and strict completed pullback

Source: localization Step 6; Stacks Tags 09AA, 099M and 099N (2),(5).
The canonical coefficient constructions are reexported from CoreA; strict tower
and Roos constructions remain in this module.
-/

@[expose] public noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section NormalizationProofs

attribute [-instance] CategoryTheory.ringedConstantTowerModulesAbelian
attribute [-instance] CategoryTheory.ringedConstantTowerTowersAbelian
attribute [-instance] CategoryTheory.ringedConstantTowerAdditive
attribute [-instance] CategoryTheory.strictTowerConstantAdditive
attribute [-instance] CategoryTheory.strictTowerLimitAdditive

attribute [local irreducible] AlgebraicGeometry.Scheme.AdicCoefficients.ringSystem
attribute [local irreducible] CategoryTheory.Limits.limit
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale WeilConjectures

namespace AlgebraicGeometry.Scheme
namespace ImmersionCompletedPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X Y : Scheme.{u}} (f : Y ⟶ X)

attribute [local irreducible] pbcIntegralDatum

/-- Identify the two strict constructions by their specified augmentation units.
Source: localization Step 6, Steps 2 and 5
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: apply moduleIso levelwise and derive its exact tower functor. The chosen
Rlim functors are the same universal right-derived limit. Their induced comparison
carries the quotient augmentation to itself, giving the displayed equation.
Completion is a reflector into complete objects, so its unit forces uniqueness. -/
theorem strictIso_exists :
    ∃! e : pbcActualStrictCompletedPull (pbcIntegralDatum l E) f ≅
        (pbcIntegralDatum l E).completedPull f,
      ∀ K : PbcCompletedDerived X (pbcIntegralDatum l E),
        (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app K ≫ e.hom.app K =
          (derivedIso l E f).hom.app K ≫ (pbcIntegralDatum l E).ordinaryToCompleted f K := by
  let d := pbcIntegralDatum l E
  let e := cbcDatumActualStrictTransport d f
  have he (K : PbcCompletedDerived X d) :
      (pbcActualStrictCompletedPullUnit d f).app K ≫ e.hom.app K =
        (derivedIso l E f).hom.app K ≫ d.ordinaryToCompleted f K := by
    rw [← ordinary_transport_eq]
    exact cbcDatumActualStrictTransport_unit d f K
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  obtain ⟨α, hα⟩ := strict_completion l E f r a ha K
  have hcomplete := (wfCompletionReflector Y d r a ha).1
    ((pbcActualDerivedPull f d).obj K)
  have hsource : WfIsComplete Y d r a ha
      ((pbcActualStrictCompletedPull d f).obj K) :=
    (wfComplete_iso Y d r a ha α).mpr hcomplete
  have htarget := (wfComplete_iso Y d r a ha (e.app K)).mp hsource
  apply (cancel_epi α.inv).mp
  apply ((wfCompletionReflector Y d r a ha).2 _ _ htarget).injective
  rw [← hα]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (he' K).trans (he K).symm


/-- The unit-normalized identification of the actual strict construction.
Source: localization Step 6, Step 5
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def strictIso := (strictIso_exists l E f).exists.choose

/-- The finite projection of the actual completed pullback, with its finite comparison.
Source: localization Step 6, Step 5
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def actualCompletedProjection
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℕ) :
    (pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj K ⟶
      (restrictedReduction l E Y n).obj
        ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K) :=
  (strictIso l E f).hom.app K ≫ completedProjection l E f K n ≫
    (restrictedComparison l E f n).hom.app K ≫
    (restrictedReduction l E Y n).map ((derivedIso l E f).inv.app K)

private theorem scalarTransition_natural (T : Scheme.{u})
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    {K L : DerivedCategory (pbcModules T R)} (a : K ⟶ L) :
    (pbcDerivedExtend φ).map a ≫ pbcReductionTransition φ ψ χ h L =
      pbcReductionTransition φ ψ χ h K ≫
        (pbcDerivedRestrict ψ).map ((pbcDerivedExtend χ).map a) := by
  let adj := pbcDerivedScalarAdjunction φ
  apply (adj.homEquiv K _).injective
  dsimp only [pbcReductionTransition]
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  simp only [Category.assoc]
  have hn := (pbcDerivedRestrictComp φ ψ χ h).inv.naturality
    ((pbcDerivedExtend χ).map a)
  dsimp only [Functor.comp_map] at hn
  have hu := (pbcDerivedScalarAdjunction χ).unit.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← hn, ← Category.assoc, hu, Category.assoc]

private theorem reductionTransition_natural (T : Scheme.{u})
    (b a : ℕ) (h : a ≤ b)
    {K L : PbcCompletedDerived T (pbcIntegralDatum l E)} (g : K ⟶ L) :
    (restrictedReduction l E T b).map g ≫ reductionTransition l E T b a h L =
      reductionTransition l E T b a h K ≫ (restrictedReduction l E T a).map g := by
  dsimp only [reductionTransition, restrictedReduction, Functor.comp_map]
  erw [← Category.assoc, ← Functor.map_comp,
    scalarTransition_natural, Functor.map_comp, Category.assoc]
  have hn := (pbcDerivedRestrictComp
    (pbcAdicProjection T (pbcIntegralDatum l E) b)
    (pbcAdicQuotient T (pbcIntegralDatum l E) b a h)
    (pbcAdicProjection T (pbcIntegralDatum l E) a)
    (pbcAdicProjection_comp T (pbcIntegralDatum l E) b a h)).hom.naturality
      ((pbcDerivedExtend (pbcAdicProjection T (pbcIntegralDatum l E) a)).map g)
  dsimp only [Functor.comp_map] at hn
  exact (congrArg (fun z ↦
    (pbcDerivedRestrict (pbcAdicProjection T (pbcIntegralDatum l E) b)).map
      (pbcReductionTransition (pbcAdicProjection T (pbcIntegralDatum l E) b)
        (pbcAdicQuotient T (pbcIntegralDatum l E) b a h)
        (pbcAdicProjection T (pbcIntegralDatum l E) a)
        (pbcAdicProjection_comp T (pbcIntegralDatum l E) b a h) K) ≫ z) hn).trans
      (Category.assoc _ _ _).symm

/-- The original strict comparison commutes with every actual finite projection.
Source: localization Step 6, Steps 2 and 5
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: combine the defining unit equation of strictIso with the unit square of
finite_compatibility and completedProjection_compatibility. Naturality of the
quotient units under derivedIso gives the first equality. The transition square
of finite_compatibility and naturality under the same isomorphism give the second,
for all quotients, including equal and successive indices. -/
theorem actualCompletedProjection_compatibility :
    (∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℕ),
      (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app K ≫
          actualCompletedProjection l E f K n =
        (reductionUnit l E Y n).app
          ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K)) ∧
    (∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (b a : ℕ) (h : a ≤ b),
      actualCompletedProjection l E f K b ≫ reductionTransition l E Y b a h
          ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K) =
        actualCompletedProjection l E f K a) := by
  constructor
  · intro K n
    dsimp only [actualCompletedProjection]
    have hs := (strictIso_exists l E f).exists.choose_spec K
    change _ ≫ (strictIso l E f).hom.app K = _ at hs
    try simp only [Category.assoc]
    erw [reassoc_of% hs,
      reassoc_of% (completedProjection_compatibility l E f).1 K n,
      reassoc_of% (finite_compatibility l E f).1 K n]
    have hn := (reductionUnit l E Y n).naturality ((derivedIso l E f).inv.app K)
    dsimp only [Functor.id_map] at hn
    erw [← hn, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  · intro K b a h
    dsimp only [actualCompletedProjection]
    try simp only [Category.assoc]
    erw [reductionTransition_natural l E Y b a h ((derivedIso l E f).inv.app K),
      ← reassoc_of% (finite_compatibility l E f).2.1 K b a h,
      reassoc_of% (completedProjection_compatibility l E f).2 K b a h]

/-- The right mate of the identity-on-constant-towers inverse-image comparison.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def rlimComparison
    (M : DerivedCategory (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E)))) :
    ((pbcIntegralDatum l E).pull f).obj
        ((completedRlim X ((pbcIntegralDatum l E).completedRing X)).obj M) ⟶
      (completedRlim Y ((pbcIntegralDatum l E).completedRing Y)).obj
        (((pbcIntegralDatum l E).towerPull f).obj M) :=
  ((pbcIntegralDatum l E).constantRlimAdjunction Y).unit.app _ ≫
    (completedRlim Y ((pbcIntegralDatum l E).completedRing Y)).map
      (((pbcIntegralDatum l E).derivedConstantPullbackIso f).inv.app _ ≫
        ((pbcIntegralDatum l E).towerPull f).map
          (((pbcIntegralDatum l E).constantRlimAdjunction X).counit.app M))

private theorem mate_augmentation
    {C D S U : Type*} [Category C] [Category D] [Category S] [Category U]
    (DX : C ⥤ S) (LX : S ⥤ C) (DY : D ⥤ U) (LY : U ⥤ D)
    (ax : DX ⊣ LX) (ay : DY ⊣ LY) (H : C ⥤ D) (T : S ⥤ U)
    (j : H ⋙ DY ⟶ DX ⋙ T) (K : C) (M : S) (i : DX.obj K ⟶ M) :
    ay.unit.app (H.obj K) ≫ LY.map (j.app K ≫ T.map i) =
      H.map (ax.unit.app K ≫ LX.map i) ≫
        (ay.unit.app (H.obj (LX.obj M)) ≫
          LY.map (j.app (LX.obj M) ≫ T.map (ax.counit.app M))) := by
  let h := ax.unit.app K ≫ LX.map i
  have hi : DX.map h ≫ ax.counit.app M = i := by
    dsimp only [h]
    rw [DX.map_comp, Category.assoc]
    have hn := ax.counit.naturality i
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [hn, ← Category.assoc]
    exact (congrArg (fun f ↦ f ≫ i) (ax.left_triangle_components K)).trans
      (Category.id_comp i)
  have hn := ay.unit.naturality (H.map h)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  have hj := j.naturality h
  dsimp only [Functor.comp_map] at hj
  change _ = H.map h ≫ _
  symm
  rw [← Category.assoc, hn, Category.assoc, ← LY.map_comp]
  congr 1
  rw [← Category.assoc, hj, Category.assoc, ← T.map_comp, hi]
  rfl

/-- The canonical completion comparison factors through this actual Rlim mate.
Source: localization Step 6, Step 5
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: expand the two constant-tower adjunction units and apply the triangle
identity. Naturality with the quotient augmentation gives precisely this equation. -/
theorem ordinaryToCompleted_eq (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :
    (pbcIntegralDatum l E).ordinaryToCompleted f K =
      ((pbcIntegralDatum l E).pull f).map ((pbcIntegralDatum l E).completionUnit X K) ≫
        rlimComparison l E f ((completedReductionTower X (pbcIntegralDatum l E)).obj K) := by
  exact mate_augmentation _ _ _ _
    ((pbcIntegralDatum l E).constantRlimAdjunction X)
    ((pbcIntegralDatum l E).constantRlimAdjunction Y)
    ((pbcIntegralDatum l E).pull f) ((pbcIntegralDatum l E).towerPull f)
    ((pbcIntegralDatum l E).derivedConstantPullbackIso f).inv K _
    ((completedReductionAugmentation (pbcIntegralDatum l E) X).app K)

/-- The ordinary module inverse image with canonical completed coefficients.
Source: localization Step 6, Step 1
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
abbrev modulePull :
    pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)) ⥤
      pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E)) := proEtaleRingModulePullback f _ _
  ((pbcIntegralDatum l E).integralRingIso f)

/-- Apply the specified ordinary inverse image to all terms of a complex.
Source: localization Step 6, Step 1
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
abbrev complexPull := (modulePull l E f).mapHomologicalComplex (.up ℤ)

/-- Apply the same inverse image to every level and transition of a strict tower complex.
Source: localization Step 6, Steps 2 and 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
abbrev towerComplexPull :=
  ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (modulePull l E f)).mapHomologicalComplex (.up ℤ)

/-- Evaluation commutes with applying inverse image term by term.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: both complexes have inverse image of M_n in every degree and inverse image
of its differential; their chain maps and differential proofs agree by extensionality. -/
theorem complexEvaluation_eq
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ)
    (n : ℕ) :
    (complexPull l E f).obj (M.asFunctor.obj (op n)) =
      ((towerComplexPull l E f).obj M).asFunctor.obj (op n) := by
  rfl

/-- The actual product comparison, determined by its projections.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def productComparison
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ) :
    (complexPull l E f).obj (strictRoosProduct M) ⟶
      strictRoosProduct ((towerComplexPull l E f).obj M) :=
  Pi.lift (f := fun n : ℕ ↦
    ((towerComplexPull l E f).obj M).asFunctor.obj (op n))
    (fun n : ℕ ↦ (complexPull l E f).map
    (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n) ≫
      eqToHom (complexEvaluation_eq l E f M n))

private theorem modulePull_preservesProducts [IsImmersion f] :
    PreservesLimitsOfShape (Discrete ℕ) (modulePull l E f) := by
  obtain ⟨_, _, _, _, _, _, h⟩ :=
    (proEtale_immersion_inverseImage_preservesLimits f).2.2
      ((pbcIntegralDatum l E).completedRing X)
  obtain ⟨P, hobj, hmap, _, _, _, hP⟩ :=
    h ((pbcIntegralDatum l E).completedRing Y) ((pbcIntegralDatum l E).integralRingIso f)
  have he : P = modulePull l E f := CategoryTheory.Functor.ext hobj hmap
  have : PreservesLimitsOfSize.{u + 1, u + 1} (modulePull l E f) := he ▸ hP
  have : PreservesLimitsOfSize.{0, 0} (modulePull l E f) :=
    preservesSmallestLimits_of_preservesLimits _
  infer_instance

/-- The coordinatewise Roos comparison, uniquely normalized by the product map.
Source: localization Step 6, Step 4; Stacks 08TC
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: inverse image preserves countable products for an immersion. Its product
comparison intertwines 1-s, since each projection gives the same pulled-back
transition. In the two Roos coordinates use this comparison on each factor.
The differentials (-dy-(1-s)x,dx) commute with this map; the inverse uses the
inverse product comparison. The coordinates jointly determine the chain map. -/
theorem roosIso_exists [IsImmersion f]
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ) :
    ∃! e : (complexPull l E f).obj (strictRoosComplex M) ≅
        strictRoosComplex ((towerComplexPull l E f).obj M),
      ∀ p : ℤ, e.hom.f (p + 1) ≫
          (strictRoosCoordinates ((towerComplexPull l E f).obj M) p).hom =
        (modulePull l E f).map (strictRoosCoordinates M p).hom ≫
          biprodComparison (modulePull l E f) _ _ ≫
            biprod.map ((productComparison l E f M).f p)
              ((productComparison l E f M).f (p + 1)) := by
  have := modulePull_preservesProducts l E f
  have hpc : productComparison l E f M = roosProductComparison (modulePull l E f) M :=
    roos_product_comparison_formula (modulePull l E f) M (complexEvaluation_eq l E f M)
  rw [hpc]
  exact roos_iso_unique (modulePull l E f) M


/-- The strict Roos isomorphism; its data is fixed on both product coordinates.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def roosIso [IsImmersion f]
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ) :=
  (roosIso_exists l E f M).exists.choose

/-- A map of strict towers gives the uniquely coordinate-normalized Roos map.
Source: localization Step 6, Step 4; Stacks 08TC
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: naturality intertwines the two transition endomorphisms. Apply the shifted
mapping-cone construction; its two coordinates give the formula and uniqueness. -/
theorem roosMap_exists (T : Scheme.{u})
    {M N : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ}
    (a : M ⟶ N) :
    ∃! b : strictRoosComplex M ⟶ strictRoosComplex N,
      ∀ p : ℤ, b.f (p + 1) ≫ (strictRoosCoordinates N p).hom =
        (strictRoosCoordinates M p).hom ≫
          biprod.map ((strictRoosProductMap a).f p) ((strictRoosProductMap a).f (p + 1)) := by
  refine ⟨roosF.map a, (fun p ↦ roosF_map_χ a p), ?_⟩
  intro b hb
  ext k : 1
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  apply (cancel_mono (strictRoosCoordinates N p).hom).1
  exact (hb p).trans (roosF_map_χ a p).symm

/-- The strict map of the actual shifted Roos cones.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def roosMap (T : Scheme.{u})
    {M N : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ}
    (a : M ⟶ N) := (roosMap_exists l E T a).exists.choose

/-- The limit embeds into Roos by its zero and compatible-sequence coordinates.
Source: localization Step 6, Step 4; Stacks 07KC
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: a compatible sequence is killed by 1-s. Therefore these coordinates commute
with the displayed Roos differential; the coordinates also give uniqueness. -/
theorem roosInclusion_exists (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :
    ∃! a : limit I.asFunctor ⟶ strictRoosComplex I,
      ∀ p : ℤ, a.f (p + 1) ≫ (strictRoosCoordinates I p).hom =
        biprod.lift 0 ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) := by
  refine ⟨roosι I, (fun p ↦ roosι_χ I p), ?_⟩
  intro a ha
  ext k : 1
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  apply (cancel_mono (strictRoosCoordinates I p).hom).1
  exact (ha p).trans (roosι_χ I p).symm

/-- The compatible-sequence inclusion, fixed on both cone coordinates.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def roosInclusion (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :=
  (roosInclusion_exists l E T I).exists.choose

/-- The termwise limit and the limit of evaluated complexes have the same projections.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: limits of complexes are computed degreewise. Their universal property in
each degree gives this chain isomorphism and determines it by its projections. -/
theorem termwiseLimitIso_exists (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :
    ∃! e : (Functor.mapHomologicalComplex
        (completedTowerLimit T ((pbcIntegralDatum l E).completedRing T))
        (.up ℤ)).obj I ≅ limit I.asFunctor,
      ∀ (n : ℕ) (p : ℤ), e.hom.f p ≫ (limit.π I.asFunctor (op n)).f p =
        limit.π (I.X p) (op n) := by
  let c := HomologicalComplex.coneOfHasLimitEval I.asFunctor
  let hc := HomologicalComplex.isLimitConeOfHasLimitEval I.asFunctor
  let e := (limit.isoLimitCone ⟨c, hc⟩).symm
  have he (n : ℕ) (p : ℤ) :
      e.hom.f p ≫ (limit.π I.asFunctor (op n)).f p =
        limit.π (I.X p) (op n) := by
    exact congrArg (fun f ↦ HomologicalComplex.Hom.f f p)
      (limit.isoLimitCone_inv_π ⟨c, hc⟩ (op n))
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply limit.hom_ext
  intro n
  ext p : 1
  exact (he' n.unop p).trans (he n.unop p).symm

/-- The projection-normalized comparison of the two ordinary limit computations.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def termwiseLimitIso (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :=
  (termwiseLimitIso_exists l E T I).exists.choose

private theorem roosMap_eq (T : Scheme.{u})
    {M N : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ}
    (a : M ⟶ N) : roosMap l E T a = roosF.map a := by
  exact (roosMap_exists l E T a).unique
    (roosMap_exists l E T a).exists.choose_spec (fun p ↦ roosF_map_χ a p)

private theorem roosInclusion_eq (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :
    roosInclusion l E T I = roosι I := by
  exact (roosInclusion_exists l E T I).unique
    (roosInclusion_exists l E T I).exists.choose_spec (fun p ↦ roosι_χ I p)

private theorem termwiseLimitIso_eq (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :
    termwiseLimitIso l E T I = ExactAdjointTowerModels.ordinaryIso.app I := by
  apply (termwiseLimitIso_exists l E T I).unique
    (termwiseLimitIso_exists l E T I).exists.choose_spec
  intro n p
  exact ExactAdjointTowerModels.ordinaryIso_components I (op n) p

/-- Roos computes the recorded Rlim, naturally and with its universal derived unit.
Source: localization Step 6, Step 4; Stacks 07KC and 08TC
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: strictRoosDerivedLimitComparison makes the inclusion a quasi-isomorphism
on a K-injective tower. The universal derived unit identifies its ordinary limit
with Rlim. Every tower has a K-injective resolution; exact countable products make
Roos carry its quasi-isomorphism to a quasi-isomorphism. Descend the normalized
zigzag along that resolution. Naturality and the formula on K-injectives force
uniqueness, independently of the chosen resolution. -/
theorem roosRlim_exists (T : Scheme.{u}) :
    ∃! e : ∀ M : CochainComplex
        (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ,
        DerivedCategory.Q.obj (strictRoosComplex M) ≅
          (completedRlim T ((pbcIntegralDatum l E).completedRing T)).obj
            (DerivedCategory.Q.obj M),
      (∀ (M N : CochainComplex
          (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) (a : M ⟶ N),
        DerivedCategory.Q.map (roosMap l E T a) ≫ (e N).hom =
          (e M).hom ≫ (completedRlim T ((pbcIntegralDatum l E).completedRing T)).map
            (DerivedCategory.Q.map a)) ∧
      (∀ (I : CochainComplex
          (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) [I.IsKInjective],
        DerivedCategory.Q.map (roosInclusion l E T I) ≫ (e I).hom =
          DerivedCategory.Q.map (termwiseLimitIso l E T I).inv ≫
            (Functor.rightDerivedFunctorObjQIso
              (completedTowerLimit T ((pbcIntegralDatum l E).completedRing T)) I).inv) := by
  classical
  let R := pbcAdicCompletion T (pbcIntegralDatum l E)
  let A := pbcModules T R
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} T
  let : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ A) :=
    reductionTower_isGrothendieckAbelian T (reductionModuleRing T R)
  let : HasExactLimitsOfShape (Discrete ℕ) A :=
    ProEt.products_exact.{u, u, 0} T (reductionModuleRing T R) ℕ
  simp only [roosMap_eq, roosInclusion_eq, termwiseLimitIso_eq]
  exact normalized_roos_iso_unique (A := A)

/-- The resolution-independent Roos identification fixed by the derived unit.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def roosRlim (T : Scheme.{u}) := (roosRlim_exists l E T).exists.choose

/-- The actual right mate is the map induced on strict Roos coordinates.
Source: localization Step 6, Steps 4 and 5
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: on strict towers inverse image commutes with both Roos coordinates by
roosIso. Normalize Roos-to-Rlim by its K-injective inclusion and universal unit.
The constant-tower adjunction mate has exactly these normalized coordinates,
so naturality on resolutions gives the displayed equation. The product maps
are invertible for immersions, hence the mate is invertible as well. -/
theorem rlimComparison_roos [IsImmersion f]
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ) :
    IsIso (rlimComparison l E f (DerivedCategory.Q.obj M)) ∧
      ((pbcIntegralDatum l E).pull f).map ((roosRlim l E X M).inv) ≫
          (modulePull l E f).mapDerivedCategoryFactors.hom.app (strictRoosComplex M) ≫
          DerivedCategory.Q.map (roosIso l E f M).hom ≫
          (roosRlim l E Y ((towerComplexPull l E f).obj M)).hom ≫
          (completedRlim Y ((pbcIntegralDatum l E).completedRing Y)).map
            (((pbcIntegralDatum l E).towerModulePull f).mapDerivedCategoryFactors.inv.app M) =
        rlimComparison l E f (DerivedCategory.Q.obj M) := by
  sorry

private theorem quotientEquiv_eq (n : ℕ) :
    quotientEquiv l E n = integralCoefficientULift l E n := by
  exact (quotientEquiv_exists l E n).unique
    (quotientEquiv_exists l E n).exists.choose_spec
    (integralCoefficientULift_exists l E n).exists.choose_spec

private theorem completedRingIso_eq (T : Scheme.{u}) :
    completedRingIso l E T = purCoefficientIso l E T := by
  apply (purCoefficientIso_existsUnique l E T).unique
  · apply (integralDetailedCoefficientComparison_exists T l E).unique
    · intro n
      have h := congrArg ((adicLisseForget T).map)
        ((completedRingIso_exists l E T).exists.choose_spec n)
      have hp : (adicLisseForget T).map
          (completedIntegralCommRingProjectionUnrestricted l E T n) =
          limit.π (integralCoefficientSheafSystem l E T) (op n) := by
        apply Sheaf.hom_ext
        ext U x
        rfl
      simpa only [Functor.map_comp, hp, Functor.mapIso_hom, completedRingIso,
        finiteRingIso, integralDetailedLevelComparison,
        quotientEquiv_eq l E] using h
    · exact (integralDetailedCoefficientComparison_exists T l E).exists.choose_spec
  · exact (purCoefficientIso_existsUnique l E T).exists.choose_spec

private theorem transport_complete_iff (T : Scheme.{u})
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E) K ↔
      IntegralOnSlice.IsComplete l E T none ((transport l E T).obj K) := by
  have h := (purCoefficientModel_predicates l E T K).1
  simpa only [transport, completedRingIso_eq l E, purCoefficientModel,
    Equivalence.changeFunctor] using h

private theorem transport_sfComplete_iff (T : Scheme.{u})
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E) K ↔
      IsSfDerivedComplete l E T ((transport l E T).obj K) := by
  have h := (purCoefficientModel_predicates l E T K).2
  simpa only [transport, completedRingIso_eq l E, purCoefficientModel,
    Equivalence.changeFunctor] using h

private theorem rlimComparison_isIso [IsImmersion f]
    (T : DerivedCategory (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E)))) :
    IsIso (rlimComparison l E f T) := by
  let d := pbcIntegralDatum l E
  let β := (mateEquiv (d.constantRlimAdjunction X) (d.constantRlimAdjunction Y)
    (TwoSquare.mk _ _ _ _ (d.derivedConstantPullbackIso f).inv)).natTrans
  have hβ (M) : β.app M = rlimComparison l E f M := by
    simp only [β, mateEquiv, Equiv.coe_fn_mk, TwoSquare.mk,
      NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      Functor.comp_map, Functor.leftUnitor_hom_app, Category.id_comp, Category.comp_id,
      rlimComparison, Functor.map_comp, Functor.map_id, Category.assoc]
    dsimp only [TwoSquare.natTrans, Functor.comp_obj]
    dsimp only [d]
    simp only [Category.id_comp, Category.comp_id]
    erw [Category.comp_id]
  let M := DerivedCategory.Q.objPreimage T
  let e : DerivedCategory.Q.obj M ≅ T := DerivedCategory.Q.objObjPreimageIso T
  have : IsIso (β.app (DerivedCategory.Q.obj M)) := by
    rw [hβ]
    exact (rlimComparison_roos l E f M).1
  have h := β.naturality e.hom
  have : IsIso ((completedRlim X (d.completedRing X) ⋙ d.pull f).map e.hom ≫ β.app T) := by
    rw [h]
    infer_instance
  rw [← hβ]
  exact IsIso.of_isIso_comp_left
    ((completedRlim X (d.completedRing X) ⋙ d.pull f).map e.hom) (β.app T)

private theorem actualStrictUnit_isIso [IsImmersion f]
    (K : PbcCompletedDerived X (pbcIntegralDatum l E))
    (hK : PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E) K) :
    IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app K) := by
  have hT := pbcIntrinsicComplete_towerComplete (pbcIntegralDatum l E) X K hK
  have : IsIso ((pbcIntegralDatum l E).completionUnit X K) := hT
  have := rlimComparison_isIso l E f
    ((completedReductionTower X (pbcIntegralDatum l E)).obj K)
  have : IsIso ((pbcIntegralDatum l E).ordinaryToCompleted f K) := by
    rw [ordinaryToCompleted_eq]
    infer_instance
  apply (isIso_comp_right_iff _ ((strictIso l E f).hom.app K)).mp
  change IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app K ≫
    (strictIso_exists l E f).exists.choose.hom.app K)
  erw [(strictIso_exists l E f).exists.choose_spec K]
  infer_instance

private theorem ordinary_preservesIntrinsic [IsImmersion f]
    (K : PbcCompletedDerived X (pbcIntegralDatum l E))
    (hK : PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E) K) :
    PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)
      ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K) := by
  have := actualStrictUnit_isIso l E f K hK
  let M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X
      (pbcIntegralDatum l E)) := ⟨K, hK⟩
  let e := (pbcActualCompletedPullback_tower (pbcIntegralDatum l E) f).exists.choose
  have he := (pbcActualCompletedPullback_tower (pbcIntegralDatum l E) f).exists.choose_spec M
  have : IsIso ((pbcActualCompletedPullUnit f (pbcIntegralDatum l E)).app K) := by
    rw [← he]
    infer_instance
  exact (actualComplete_iso Y (pbcIntegralDatum l E)
    (asIso ((pbcActualCompletedPullUnit f (pbcIntegralDatum l E)).app K))).mpr
    (pbcActualCompletedPull_isComplete f (pbcIntegralDatum l E) K)

private theorem immersion_completed_pullback_comparison_complete [IsImmersion f] :
    (∀ K : PbcCompletedDerived X (pbcIntegralDatum l E),
      IntegralOnSlice.IsComplete l E X none ((transport l E X).obj K) →
        (pbcIntegralDatum l E).TowerComplete X K ∧
        IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app K) ∧
        IntegralOnSlice.IsComplete l E Y none
          ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K))) := by
  intro K hK
  have hX := (transport_complete_iff l E X K).mpr hK
  exact ⟨pbcIntrinsicComplete_towerComplete (pbcIntegralDatum l E) X K hX,
    actualStrictUnit_isIso l E f K hX,
    (transport_complete_iff l E Y _).mp (ordinary_preservesIntrinsic l E f K hX)⟩

private theorem immersion_completed_pullback_comparison_constructible [IsImmersion f] :
    ∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (r s : ℤ),
      r ≤ s → sfIntegralConstructible l E X ((transport l E X).obj K) →
      (∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj
          ((transport l E X).obj K)) ⊆ Set.Icc r s) →
      sfIntegralConstructible l E Y
        ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K)) ∧
      ∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension.{u, u} l E Y n).obj
          ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K))) ⊆
            Set.Icc r s := by
  intro K r s hrs hK hb
  obtain ⟨hcomplete, a, b, hab, hfinite⟩ := hK
  have hX := (transport_sfComplete_iff l E X K).mpr hcomplete
  have hY := (transport_sfComplete_iff l E Y _).mp
    (ordinary_preservesIntrinsic l E f K hX)
  refine ⟨⟨hY, a, b, hab, ?_⟩, ?_⟩
  · intro n
    exact finite_reduction_preservesConstructibleInterval l E f K n a b (hfinite n)
  · intro n
    exact (finite_reduction_preservesConstructibleInterval l E f K n r s
      ⟨(hfinite n).1, hb n⟩).2

private theorem actualModulePull_finiteLimits [IsImmersion f] :
    PreservesFiniteLimits (pbcActualModulePull f (pbcIntegralDatum l E)) := by
  exact completedModulePullback_finiteLimits f (pbcIntegralDatum l E)

private theorem actualModulePull_finiteColimits [IsImmersion f] :
    PreservesFiniteColimits (pbcActualModulePull f (pbcIntegralDatum l E)) := by
  exact completedModulePullback_finiteColimits f (pbcIntegralDatum l E)

/-- Ordinary immersion inverse image is exact and preserves the specified complete
objects; the actual strict-tower unit is invertible on every derived-complete input.
The last clause uses the recorded integral category and keeps the given interval.
Source: localization Step 6; Stacks 09AA, 099M and 099N (2),(5)
(blueprint: lem-sf-immersion-completed-pullback-comparison).

Proof plan, following the node's Steps 1--6:
1. Identify completed and finite inverse-image coefficients by
   lem-weil-pbc-profinite-coefficient-inverse-image. Use
   lem-weil-pbc-proetale-immersion-limit-preservation for exactness and products;
   lem-sf-exact-functor-derived-triangulated identifies exact descent with Lu*.
2. Choose one flat-term K-flat representative. The canonical tensor-pullback
   comparisons of lem-weil-pbc-ringed-topoi-derived-tensor-pullback and
   lem-weil-pbc-ringed-topoi-module-pullback-tensor identify its strict quotient
   towers, including their augmentation and all quotient maps.
3. The finite-extension DVR gives the Noetherian adic datum (its quotients are
   finite and perfect). Use lem-weil-pbc-constant-completion-equivalence,
   lem-weil-pbc-ringed-koszul-completion-reflector and
   lem-weil-derived-limit-existence to show that the actual source completion
   unit, rather than an arbitrary isomorphism, is invertible. The signed
   Koszul-fibre-to-Roos identification carries the intrinsic unit to this unit.
4. Exact countable products (lem-weil-proetale-countable-products-exact) and
   lem-sf-strict-roos-derived-limit-comparison compute total inverse limit.
   Its inverse-image comparison is roosIso, with productComparison on both
   coordinates and the second coordinate as every finite projection.
5. The quotient augmentation is p mapped to (0,(p tensor 1)_n). Its image is
   the same augmentation for the pulled-back tower. Thus the specified strict
   completed-pullback comparison is the pullback of the source completion
   unit followed by this Roos comparison. All finite and successive quotient
   squares commute by finite_compatibility. This also gives completeness.
6. Use lem-sf-proetale-constructible-origin and
   lem-weil-pbc-pullback-preserves-bounded-constructible on every reduction.
   Each has exactly the original interval [r,s]. Together with completeness
   this is sfIntegralConstructible, with no additional boundedness condition. -/
theorem immersion_completed_pullback_comparison [IsImmersion f] :
    PreservesFiniteLimits (pbcActualModulePull f (pbcIntegralDatum l E)) ∧
    PreservesFiniteColimits (pbcActualModulePull f (pbcIntegralDatum l E)) ∧
    PreservesLimitsOfShape (Discrete ℕ) (modulePull l E f) ∧
    (∀ K : PbcCompletedDerived X (pbcIntegralDatum l E),
      IntegralOnSlice.IsComplete l E X none ((transport l E X).obj K) →
        (pbcIntegralDatum l E).TowerComplete X K ∧
        IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app K) ∧
        IntegralOnSlice.IsComplete l E Y none
          ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K))) ∧
    (∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (r s : ℤ),
      r ≤ s → sfIntegralConstructible l E X ((transport l E X).obj K) →
      (∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj
          ((transport l E X).obj K)) ⊆ Set.Icc r s) →
      sfIntegralConstructible l E Y
        ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K)) ∧
      ∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension.{u, u} l E Y n).obj
          ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K))) ⊆
            Set.Icc r s)   := by
  let hL := actualModulePull_finiteLimits l E f
  let hC := actualModulePull_finiteColimits l E f
  refine ⟨hL, hC, modulePull_preservesProducts l E f,
    immersion_completed_pullback_comparison_complete l E f,
    immersion_completed_pullback_comparison_constructible l E f⟩

end ImmersionCompletedPullback
end AlgebraicGeometry.Scheme

end NormalizationProofs
