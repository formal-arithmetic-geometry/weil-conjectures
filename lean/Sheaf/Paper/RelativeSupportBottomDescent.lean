/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.PbcCoefficientTwists
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
public import Sheaf.AlgebraicGeometry.SupportSiteComparison
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

import all WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.CategoryTheory.RightDerivedInjectiveSequence
import WeilConjectures.CategoryTheory.RightDerivedZeroTransformation
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.CategoryTheory.Sites.SectionsWithSupport
import all Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction
import all Sheaf.CategoryTheory.ModuleRestrictionKernelComparison
import Sheaf.AlgebraicGeometry.GeometricStalkCohomology
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.CategoryTheory.GrothendieckEdgeCocycle
import Sheaf.CategoryTheory.FirstQuadrantLowestRowEdge
import Sheaf.AlgebraicGeometry.KunnethSupported
import Sheaf.Paper.RelativeSupportCoordinateModel
import Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates
import Sheaf.Paper.PurTwistSheafLocallyFree
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.Paper.PurityRankOneLocalCalculation
import Sheaf.CategoryTheory.GrothendieckSpectralSequence
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted

/-! # Descent in the bottom supported degree of a smooth pair

Source: Stacks Project, Tag 09XP, section-cohomology-support; the relative smooth-pair
refinement in the blueprint (blueprint: lem-pur-relative-support-bottom-descent).

The support cohomology sheaf is formed on the fixed site of U by deriving the actual
closed-support kernel. Kernel-normalized comparison identifies its evaluation-derived
functors with the recorded supported-cohomology groups on etale objects. The edge is
natural in these objects. The pro-etale comparison derives the published adjunction-unit
map on support kernels, and descent tests global supported classes on an arbitrary cover.

The canonical support, evaluation, scalar-forgetting and site-comparison interfaces
are proved below. The remaining smooth-pair vanishing and descent obligation is the
named final theorem, with its proof plan recorded in the declaration and DAG node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- The finite coefficient sheaf with an arbitrary signed Tate index.
Source: the coefficient datum and signed finite Tate sheaf (blueprint:
lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportCoefficient
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) (r : ℤ) :
    Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (P.forgetEtale T).obj
    (Scheme.finiteEtaleTateSheaf P.Coefficient (ringChar P.Coefficient) T
      (CharP.cast_eq_zero P.Coefficient (ringChar P.Coefficient)) r)

/-- The sheaf-valued closed-support kernel on the small étale site.
Source: Stacks Tag 09XP and the support-kernel construction (blueprint:
lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportKernel {Z U : Scheme.{u}} (i : Z ⟶ U)
    [IsClosedImmersion i] :
    Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  supportedKernel i.openComplement.ι

/-- Additivity of the closed-support kernel, needed for its right-derived functor.
Source: Stacks Tag 09XQ (blueprint: lem-pur-relative-support-bottom-descent).
Proof: the support kernel is a pointwise kernel in an abelian sheaf category; compose
the additivity equation with the kernel inclusion and cancel its monomorphism. -/
@[instance] theorem relativeSupportKernel_additive
    {Z U : Scheme.{u}} (i : Z ⟶ U) [IsClosedImmersion i] :
    (relativeSupportKernel i).Additive := by
  exact Functor.additive_of_iso (supportedKernelIso i.openComplement.ι).symm

/-- The local cohomology sheaf in degree `b` of the signed coefficient `A(r)`.
Source: Stacks Tag 09XP, derived sheaf of sections with support (blueprint:
lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportCohomologySheaf
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z U : Scheme.{u}} (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (b : ℤ) :
    Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (DerivedCategory.Plus.homologyFunctor
      (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) b).obj
    ((relativeSupportKernel i).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (relativeSupportCoefficient P U r)))

private theorem relativeSupportKernel_preservesInjectives
    {Z U : Scheme.{u}} (i : Z ⟶ U) [IsClosedImmersion i] :
    (relativeSupportKernel i).PreservesInjectiveObjects := by
  obtain ⟨hu, hl, _, ⟨adj⟩⟩ := supportedKernel_closedAdjunction i i.openComplement.ι
    (by
      rw [i.range_eq_compl_range_openComplement_ι]
      exact (isCompl_compl : IsCompl (Set.range i.openComplement.ι.base)
        (Set.range i.openComplement.ι.base)ᶜ).symm)
  have := adj.preservesInjectiveObjects_of_preservesFiniteLimits
  have : IsIso (Functor.whiskerLeft (supportedKernel i.openComplement.ι)
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit) := hu
  constructor
  intro I hI
  let e := asIso (Functor.whiskerLeft (supportedKernel i.openComplement.ι)
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit)
  exact Injective.of_iso (e.app I).symm
    ((lowerStar AddCommGrpCat.{u + 1} i).injective_obj
      ((supportedClosedInverseImage i i.openComplement.ι).obj I))

set_option linter.unusedVariables false in
/-- The support/global-sections pair is acyclic on injectives.
Source: Stacks Tag 09XP, section-cohomology-support, and Tag 09XQ,
lemma-sections-with-support-acyclic (blueprint: lem-pur-relative-support-bottom-descent).
Proof: the closed-support adjunction writes P_Z as i_* i^!_0. Exact closed direct
image and its two adjunctions make both factors preserve injectives. Therefore
P_Z sends injectives to injectives, which are acyclic for global sections. -/
theorem relativeSupport_isAcyclic
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z U : Scheme.{u}} (i : Z ⟶ U) [IsClosedImmersion i] :
    (relativeSupportKernel i).IsAcyclicComposablePair
      (Sheaf.Γ U.smallEtaleTopology AddCommGrpCat.{u + 1}) := by
  have := relativeSupportKernel_preservesInjectives i
  exact Functor.isAcyclicComposablePair_of_preservesInjectiveObjects _ _

/-- Evaluation at one etale object of the fixed site of U.
Source: Stacks Tag 09XP, the functor Gamma(W,-)
(blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable abbrev relativeSupportEvaluation {U : Scheme.{u}} (W : U.Etale) :
    Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ _).obj (op W)

/-- Restriction of evaluation along a morphism of the fixed etale site.
Source: Stacks Tag 09XP, restriction of sections
(blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportEvaluationMap {U : Scheme.{u}} {W W' : U.Etale}
    (a : W' ⟶ W) : relativeSupportEvaluation W ⟶ relativeSupportEvaluation W' :=
  Functor.whiskerLeft (sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    ((CategoryTheory.evaluation U.Etaleᵒᵖ AddCommGrpCat.{u + 1}).map a.op)

/-- Etale restriction, computed by the existing localization functor.
Source: Stacks Tag 03F3, localization of the small etale site
(blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable abbrev relativeSupportRestriction {U : Scheme.{u}} (W : U.Etale) :=
  localizationRestriction AddCommGrpCat.{u + 1} W.hom inferInstance

/-- Terminal evaluation of localization is evaluation at W.
Source: Stacks Tag 03F3 (blueprint: lem-pur-relative-support-bottom-descent).
Proof: localization composes the identity of W with W -> U. The identity law and
extensionality of objects of the etale over-category give the equality. -/
theorem relativeSupport_terminal {U : Scheme.{u}} (W : U.Etale) :
    (MorphismProperty.Over.map ⊤ (inferInstance : Etale W.hom)).obj
      (Scheme.Etale.mk (𝟙 W.left)) = W := by
  cases W
  congr 1

/-- The canonical evaluation identification, using only the identity law of localization.
Source: Stacks Tag 03F3 (blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportSectionIso {U : Scheme.{u}} (W : U.Etale)
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    F.obj.obj (op W) ≅
      ((relativeSupportRestriction W).obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 W.left))) :=
  F.obj.mapIso (eqToIso (relativeSupport_terminal W)).op

/-- The support/evaluation pair is acyclic on injectives on the fixed site U.
Source: Stacks Tags 09XP, 09XQ and 015N
(blueprint: lem-pur-relative-support-bottom-descent).
Proof: the closed-support adjunction makes its kernel send injectives to injectives;
evaluation at W has no positive derived functors on injectives. Equivalently restrict
an injective to W, using exact etale extension by zero, and take global sections. -/
theorem relativeSupport_evaluationAcyclic {Z U : Scheme.{u}} (i : Z ⟶ U)
    [IsClosedImmersion i] (W : U.Etale) :
    (relativeSupportKernel i).IsAcyclicComposablePair (relativeSupportEvaluation W) := by
  have := relativeSupportKernel_preservesInjectives i
  exact Functor.isAcyclicComposablePair_of_preservesInjectiveObjects _ _

private theorem relativeSupportEtaleIso {T : Scheme.{u}} {V W : T.Etale}
    (a : V ⟶ W) (ha : IsIso a.left) : IsIso a := by
  have : IsIso ((Over.forget T).map ((Scheme.Etale.forget T).map a)) := ha
  have : IsIso ((Scheme.Etale.forget T).map a) :=
    isIso_of_reflects_iso _ (Over.forget T)
  exact isIso_of_reflects_iso a (Scheme.Etale.forget T)

private theorem relativeSupportEvaluationKernel_iff {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (W : U.Etale)
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V : AddCommGrpCat.{u + 1}} (φ : V ⟶ F.obj.obj (op W)) :
    φ ≫ ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      i.openComplement.ι).unit.app F).hom.app (op W) = 0 ↔
    φ ≫ (relativeSupportSectionIso W F).hom ≫
      (((relativeSupportRestriction W).obj F).obj.map
        (supportRestrictionArrow (pullback.snd i W.hom)).op) = 0 := by
  let A := AddCommGrpCat.{u + 1}
  let j := i.openComplement.ι
  let i' := pullback.snd i W.hom
  let j' := i'.openComplement.ι
  let M := MorphismProperty.Over.map ⊤ (inferInstance : Etale W.hom)
  let D := (MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj
    ((MorphismProperty.Over.pullback @Etale ⊤ j).obj W)
  let b : D ⟶ W := (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j
    inferInstance trivial).counit.app W
  have hrange : Set.range j' = Set.range (pullback.fst W.hom j) := by
    rw [IsOpenImmersion.range_pullbackFst]
    change Set.range i'.openComplement.ι = W.hom ⁻¹' Set.range j
    rw [← compl_compl (Set.range i'.openComplement.ι),
      ← i'.range_eq_compl_range_openComplement_ι]
    dsimp [i']
    rw [Scheme.Pullback.range_snd, i.range_eq_compl_range_openComplement_ι]
    simp only [Set.preimage_compl, compl_compl]
    rfl
  let e := IsOpenImmersion.isoOfRangeEq j' (pullback.fst W.hom j) hrange
  let h : M.obj (Scheme.Etale.mk j') ⟶ D := MorphismProperty.Over.homMk e.hom (by
    change e.hom ≫ pullback.snd W.hom j ≫ j = j' ≫ W.hom
    rw [← pullback.condition, ← Category.assoc,
      IsOpenImmersion.isoOfRangeEq_hom_fac])
  have : IsIso h := relativeSupportEtaleIso h (by change IsIso e.hom; infer_instance)
  have hfac : h ≫ b = M.map (supportRestrictionArrow i') ≫
      (eqToIso (relativeSupport_terminal W)).hom := by
    apply MorphismProperty.Over.Hom.ext
    change e.hom ≫ pullback.fst W.hom j = _
    rw [IsOpenImmersion.isoOfRangeEq_hom_fac]
    have ht : ((eqToIso (relativeSupport_terminal W)).hom).left = 𝟙 W.left := by
      change (Scheme.Etale.forget U ⋙ Over.forget U).map
        (eqToHom (relativeSupport_terminal W)) = _
      rw [eqToHom_map]
      rfl
    change j' = j' ≫ ((eqToIso (relativeSupport_terminal W)).hom).left
    rw [ht]
    exact (Category.comp_id j').symm
  have hcomp : (relativeSupportSectionIso W F).hom ≫
      (((relativeSupportRestriction W).obj F).obj.map (supportRestrictionArrow i').op) =
        F.obj.map b.op ≫ F.obj.map h.op := by
    change F.obj.map (eqToIso (relativeSupport_terminal W)).hom.op ≫
      F.obj.map (M.map (supportRestrictionArrow i')).op = _
    rw [← F.obj.map_comp, ← op_comp, ← hfac, op_comp, F.obj.map_comp]
  let adj := upperStarLowerStarAdjunction A j
  let adj' := localizationRestrictionLowerStarAdjunction A j inferInstance
  let c := adj.leftAdjointUniq adj'
  have hu : adj.unit.app F = adj'.unit.app F ≫ (lowerStar A j).map (c.inv.app F) := by
    have h := congrArg (fun k ↦ k ≫ (lowerStar A j).map (c.inv.app F))
      (adj.unit_leftAdjointUniq_hom_app adj' F)
    change (adj.unit.app F ≫ (lowerStar A j).map (c.hom.app F)) ≫
      (lowerStar A j).map (c.inv.app F) = _ at h
    rw [Category.assoc, ← Functor.map_comp] at h
    erw [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id] at h
    exact h
  rw [show (upperStarLowerStarAdjunction A j).unit.app F = _ from hu]
  change φ ≫ F.obj.map b.op ≫
    ((lowerStar A j).map (c.inv.app F)).hom.app (op W) = 0 ↔ _
  rw [hcomp]
  constructor <;> intro hv
  · rw [← Category.assoc] at hv ⊢
    have hz : φ ≫ F.obj.map b.op = 0 := by
      rw [← cancel_mono (((lowerStar A j).map (c.inv.app F)).hom.app (op W)),
        hv, zero_comp]
    rw [hz, zero_comp]
  · rw [← Category.assoc] at hv ⊢
    have hz : φ ≫ F.obj.map b.op = 0 := by
      rw [← cancel_mono (F.obj.map h.op), hv, zero_comp]
    rw [hz, zero_comp]

private noncomputable def relativeSupportEvaluationKernelLimit {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (W : U.Etale)
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  let η := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i.openComplement.ι).unit
  let H := ((CategoryTheory.evaluation _ _).obj F) ⋙ relativeSupportEvaluation W
  KernelFork.isLimitOfIsLimitOfIff
    (KernelFork.mapIsLimit _ (kernelIsKernel η) H)
    (((relativeSupportRestriction W).obj F).obj.map
      (supportRestrictionArrow (pullback.snd i W.hom)).op)
    (relativeSupportSectionIso W F) (fun {_} φ ↦ relativeSupportEvaluationKernel_iff i W F φ)

/-- The support kernel evaluated at W is the support kernel on W of the restriction.
The displayed inclusion equation determines the isomorphism uniquely, so no choice
of supported class or orientation is made.
Source: Stacks Tag 09XP, kernel formula, and Tag 03F3
(blueprint: lem-pur-relative-support-bottom-descent).
Proof: both sides are the kernel of restriction F(W) -> F(W minus Z_W).
Localization identifies these restriction arrows. The kernel universal property gives
both maps, and their inclusion equations prove they are inverse and natural. -/
theorem relativeSupportEvaluationIso_existsUnique {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (W : U.Etale) :
    ∃! e : relativeSupportKernel i ⋙ relativeSupportEvaluation W ≅
      relativeSupportRestriction W ⋙ supportSections (pullback.snd i W.hom),
      ∀ F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1},
        e.hom.app F ≫ kernel.ι
          (((relativeSupportRestriction W).obj F).obj.map
            (supportRestrictionArrow (pullback.snd i W.hom)).op) =
        (relativeSupportEvaluation W).map
          ((kernel.ι (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
            i.openComplement.ι).unit).app F) ≫
          (relativeSupportSectionIso W F).hom := by
  let β := relativeSupportRestriction W
  let K := relativeSupportKernel i ⋙ relativeSupportEvaluation W
  let S := β ⋙ supportSections (pullback.snd i W.hom)
  let E := β ⋙ relativeSupportEvaluation (Scheme.Etale.mk (𝟙 W.left))
  let α : relativeSupportEvaluation W ≅ E :=
    NatIso.ofComponents (relativeSupportSectionIso W)
      (by intro F G a; exact (a.hom.naturality
        (eqToIso (relativeSupport_terminal W)).hom.op).symm)
  let ι : K ⟶ E := Functor.whiskerRight (kernel.ι
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i.openComplement.ι).unit)
      (relativeSupportEvaluation W) ≫ α.hom
  let κ : S ⟶ E := Functor.whiskerLeft β (Sheaf.supportedSectionsInclusion
    W.left.smallEtaleTopology AddCommGrpCat.{u + 1}
      (supportRestrictionArrow (pullback.snd i W.hom)))
  let eF (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    (relativeSupportEvaluationKernelLimit i W F).conePointUniqueUpToIso
      (kernelIsKernel (((relativeSupportRestriction W).obj F).obj.map
        (supportRestrictionArrow (pullback.snd i W.hom)).op))
  have heF (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :
      (eF F).hom ≫ κ.app F = ι.app F :=
    (relativeSupportEvaluationKernelLimit i W F).conePointUniqueUpToIso_hom_comp
      (kernelIsKernel (((relativeSupportRestriction W).obj F).obj.map
        (supportRestrictionArrow (pullback.snd i W.hom)).op)) WalkingParallelPair.zero
  let e : K ≅ S := NatIso.ofComponents eF (by
    intro F G a
    have : Mono (κ.app G) := by
      change Mono (kernel.ι _)
      infer_instance
    apply (cancel_mono (κ.app G)).1
    simp only [Category.assoc]
    rw [heF, show S.map a ≫ κ.app G = κ.app F ≫ E.map a from κ.naturality a,
      ← Category.assoc, heF]
    exact ι.naturality a)
  refine ⟨e, heF, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext F
  have : Mono (κ.app F) := by
      change Mono (kernel.ι _)
      infer_instance
  apply (cancel_mono (κ.app F)).1
  exact (he' F).trans (heF F).symm

/-- The unique kernel-normalized support/evaluation comparison.
Source: Stacks Tag 09XP (blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportEvaluationIso {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (W : U.Etale) :=
  Classical.choose (relativeSupportEvaluationIso_existsUnique i W)

/-- Exactness and additivity of the existing etale localization restriction.
Source: Stacks Tag 03F3 (blueprint: lem-pur-relative-support-bottom-descent).
Proof: restriction is computed sectionwise and is canonically the exact inverse image.
Transport exactness along upperStarIsoLocalizationRestriction; addition is sectionwise. -/
@[instance] theorem relativeSupportRestriction_additive {U : Scheme.{u}} (W : U.Etale) :
    (relativeSupportRestriction W).Additive := by
  exact Functor.additive_of_iso
    (upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} W.hom inferInstance)

/-- Exactness of etale restriction, for deriving the kernel-normalized comparison.
Source: Stacks Tag 03F3 (blueprint: lem-pur-relative-support-bottom-descent).
Proof: the localization functor is the inverse image, hence exact. -/
@[instance] theorem relativeSupportRestriction_colimits {U : Scheme.{u}} (W : U.Etale) :
    PreservesFiniteColimits (relativeSupportRestriction W) := by
  exact preservesFiniteColimits_of_natIso
    (upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} W.hom inferInstance)

/-- Left exactness of etale restriction.
Source: Stacks Tag 03F3 (blueprint: lem-pur-relative-support-bottom-descent).
Proof: limits are computed sectionwise, so restriction preserves finite limits. -/
@[instance] theorem relativeSupportRestriction_limits {U : Scheme.{u}} (W : U.Etale) :
    PreservesFiniteLimits (relativeSupportRestriction W) := by
  exact preservesFiniteLimits_of_natIso
    (upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} W.hom inferInstance)

/-- The derived restriction comparison attached to the kernel-normalized ordinary map.
Source: Stacks Tags 09XP and 015N
(blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportDerivedEvaluation {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (W : U.Etale) (n : ℕ) :=
  Functor.rightDerivedBaseChange
    (β := relativeSupportRestriction W) (γ := 𝟭 AddCommGrpCat.{u + 1})
    ((Functor.rightUnitor _).hom ≫ (relativeSupportEvaluationIso i W).hom) n

private theorem relativeSupportSections_limits {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] : PreservesFiniteLimits (supportSections i) := by
  let F := relativeSupportEvaluation (Scheme.Etale.mk (𝟙 T))
  let G := relativeSupportEvaluation (Scheme.Etale.mk i.openComplement.ι)
  let a : F ⟶ G := relativeSupportEvaluationMap (supportRestrictionArrow i)
  let ι : supportSections i ⟶ F :=
    { app := fun M ↦ kernel.ι (a.app M)
      naturality := by intro M N f; exact kernel.lift_ι _ _ _ }
  have : ∀ M, Mono (ι.app M) := fun M ↦ by dsimp [ι]; infer_instance
  exact ModuleRestrictionKernel.kernelLeftExact F G (supportSections i) a ι
    (fun M ↦ kernel.condition _) (fun M ↦ kernelIsKernel _)

/-- Derived evaluation identifies the recorded supported cohomology on W with the
cohomology computed using injectives on U.
Source: Stacks Tags 03F3 and 09XP
(blueprint: lem-pur-relative-support-bottom-descent).
Proof: etale restriction preserves injectives, since its etale extension-by-zero left
adjoint is exact. Apply the ordinary kernel comparison termwise to an injective
resolution on U. This computes both derived functors and the stated base-change map. -/
@[instance] theorem relativeSupportDerivedEvaluation_isIso {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (W : U.Etale) (n : ℕ) :
    IsIso (relativeSupportDerivedEvaluation i W n) := by
  have := relativeSupportSections_limits (pullback.snd i W.hom)
  let β := relativeSupportRestriction W
  let e : (relativeSupportKernel i ⋙ relativeSupportEvaluation W) ⋙
      𝟭 AddCommGrpCat.{u + 1} ≅
      β ⋙ supportSections (pullback.snd i W.hom) :=
    (Functor.rightUnitor _) ≪≫ relativeSupportEvaluationIso i W
  have hβ (I : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective I] :
      Injective (β.obj I) := by
    exact Injective.of_iso
      ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} W.hom
        inferInstance).app I)
      (by
        have : PreservesFiniteLimits
            (etaleLowerShriek AddCommGrpCat.{u + 1} W.hom inferInstance) := by
          change PreservesFiniteLimits
            (sheafToPresheaf W.left.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
              (MorphismProperty.Over.map ⊤ (inferInstance : Etale W.hom)).op.lan ⋙
                presheafToSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
          have : PreservesFiniteLimits
              ((MorphismProperty.Over.map ⊤ (inferInstance : Etale W.hom)).op.lan :
                (W.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
                  U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
            SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian _ _
          infer_instance
        exact (etaleLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1} W.hom
          inferInstance).map_injective I inferInstance)
  have : PreservesFiniteLimits β := relativeSupportRestriction_limits W
  have : PreservesFiniteColimits β := relativeSupportRestriction_colimits W
  have : IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (β := β) (γ := 𝟭 AddCommGrpCat.{u + 1}) e.hom) :=
    Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
      (β := β) (γ := 𝟭 AddCommGrpCat.{u + 1}) e
      (fun I _ ↦ by
        have := hβ I
        exact Functor.rightAcyclic_of_injective _)
  change IsIso (Functor.rightDerivedBaseChange
    (β := β) (γ := 𝟭 AddCommGrpCat.{u + 1}) e.hom n)
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  rw [Functor.rightDerivedBaseChange_app]
  infer_instance

/-- The canonical local-to-global edge, with target the same cohomology sheaf on U
at every W. The last factor is the existing natural-number/integer derived comparison.
Source: Stacks Tag 09XP and Tag 015N
(blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportEdge
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (n : ℕ) (W : U.Etale) :
    supportCohomology (pullback.snd i W.hom) n
        ((relativeSupportRestriction W).obj (relativeSupportCoefficient P U r)) ⟶
      (relativeSupportCohomologySheaf P i r n).obj.obj (op W) :=
  (asIso (relativeSupportDerivedEvaluation i W n)).inv.app
      (relativeSupportCoefficient P U r) ≫
    ((relativeSupportKernel i).grothendieckLeftEdgeMap (relativeSupportEvaluation W)
      (relativeSupport_evaluationAcyclic i W) n).app (relativeSupportCoefficient P U r) ≫
    (relativeSupportEvaluation W).map
      (((relativeSupportKernel i).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
        n).inv.app (relativeSupportCoefficient P U r))

/-- Restriction of supported cohomology, using the same injective resolution on U.
Its transports to the recorded W-side groups are the kernel-normalized derived maps.
Source: Stacks Tag 09XP (blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportClassRestriction
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (n : ℕ) {W W' : U.Etale}
    (a : W' ⟶ W) :
    supportCohomology (pullback.snd i W.hom) n
        ((relativeSupportRestriction W).obj (relativeSupportCoefficient P U r)) ⟶
      supportCohomology (pullback.snd i W'.hom) n
        ((relativeSupportRestriction W').obj (relativeSupportCoefficient P U r)) :=
  (asIso (relativeSupportDerivedEvaluation i W n)).inv.app
      (relativeSupportCoefficient P U r) ≫
    (NatTrans.rightDerived
      (Functor.whiskerLeft (relativeSupportKernel i) (relativeSupportEvaluationMap a)) n).app
        (relativeSupportCoefficient P U r) ≫
    (relativeSupportDerivedEvaluation i W' n).app (relativeSupportCoefficient P U r)

private theorem relativeSupportGlobalUnitFactor {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i]
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ q : F.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)) ≅
        ((upperStar AddCommGrpCat.{u + 1} i.openComplement.ι ⋙
          lowerStar AddCommGrpCat.{u + 1} i.openComplement.ι).obj F).obj.obj
            (op (Scheme.Etale.mk (𝟙 U))),
      F.obj.map (supportRestrictionArrow i).op ≫ q.hom =
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          i.openComplement.ι).unit.app F).hom.app (op (Scheme.Etale.mk (𝟙 U))) := by
  let A := AddCommGrpCat.{u + 1}
  let j := i.openComplement.ι
  let a := (Scheme.Etale.isTerminalMkId U).from (Scheme.Etale.mk j)
  have heq : a = supportRestrictionArrow i := (Scheme.Etale.isTerminalMkId U).hom_ext _ _
  have hmono : IsIso ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j
      inferInstance trivial).counit.app (Scheme.Etale.mk j)) := by
    apply relativeSupportEtaleIso
    change IsIso (pullback.fst j j)
    infer_instance
  have hbase : IsIso ((MorphismProperty.Over.pullback @Etale ⊤ j).map a) := by
    apply relativeSupportEtaleIso
    have h := MorphismProperty.Over.w ((MorphismProperty.Over.pullback @Etale ⊤ j).map a)
    have : IsIso ((MorphismProperty.Over.pullback @Etale ⊤ j).obj
        (Scheme.Etale.mk j)).hom := inferInstanceAs (IsIso (pullback.snd j j))
    have : IsIso ((MorphismProperty.Over.pullback @Etale ⊤ j).obj
        (Scheme.Etale.mk (𝟙 U))).hom := inferInstanceAs (IsIso (pullback.snd (𝟙 U) j))
    exact IsIso.of_isIso_fac_right h
  let adj := openImmersionRestrictionLowerStarAdjunction A j
  let Q := (lowerStar A j).obj ((openImmersionRestriction A j).obj F)
  have hη : IsIso ((adj.unit.app F).hom.app (op (Scheme.Etale.mk j))) :=
    inferInstanceAs (IsIso (𝟙 _ ≫ F.obj.map
      ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance trivial).counit.app
        (Scheme.Etale.mk j)).op ≫ 𝟙 _))
  have hr : IsIso (Q.obj.map a.op) := by
    change IsIso (((openImmersionRestriction A j).obj F).obj.map
      ((MorphismProperty.Over.pullback @Etale ⊤ j).map a).op)
    infer_instance
  let e := (upperStarLowerStarAdjunction A j).leftAdjointUniq adj
  let q := asIso ((adj.unit.app F).hom.app (op (Scheme.Etale.mk j))) ≪≫
    (asIso (Q.obj.map a.op)).symm ≪≫
    (relativeSupportEvaluation (Scheme.Etale.mk (𝟙 U))).mapIso
      ((lowerStar A j).mapIso (e.symm.app F))
  refine ⟨q, ?_⟩
  dsimp [q]
  rw [← heq, reassoc_of% (adj.unit.app F).hom.naturality a.op]
  change (adj.unit.app F).hom.app _ ≫ Q.obj.map a.op ≫
    inv (Q.obj.map a.op) ≫ _ = _
  rw [IsIso.hom_inv_id_assoc]
  change ((adj.unit.app F) ≫ (lowerStar A j).map (e.inv.app F)).hom.app _ = _
  have hunit : adj.unit.app F ≫ (lowerStar A j).map (e.inv.app F) =
      (upperStarLowerStarAdjunction A j).unit.app F := by
    rw [← Adjunction.unit_leftAdjointUniq_hom_app
      (upperStarLowerStarAdjunction A j) adj F]
    change (_ ≫ (lowerStar A j).map (e.hom.app F)) ≫
      (lowerStar A j).map (e.inv.app F) = _
    rw [Category.assoc, ← Functor.map_comp, e.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id]
  exact congrArg (fun a ↦ a.hom.app (op (Scheme.Etale.mk (𝟙 U)))) hunit

private theorem relativeSupportGlobalKernel_condition {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i]
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (relativeSupportEvaluation (Scheme.Etale.mk (𝟙 U))).map
        ((kernel.ι (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          i.openComplement.ι).unit).app F) ≫
      F.obj.map (supportRestrictionArrow i).op = 0 := by
  obtain ⟨q, hq⟩ := relativeSupportGlobalUnitFactor i F
  let H := ((CategoryTheory.evaluation _ _).obj F) ⋙
    relativeSupportEvaluation (Scheme.Etale.mk (𝟙 U))
  rw [← cancel_mono q.hom, Category.assoc, hq, zero_comp]
  change H.map (kernel.ι (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    i.openComplement.ι).unit) ≫ H.map
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i.openComplement.ι).unit = 0
  rw [← H.map_comp, kernel.condition, H.map_zero]

private noncomputable def relativeSupportGlobalKernelLimit {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i]
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsLimit (KernelFork.ofι _ (relativeSupportGlobalKernel_condition i F)) := by
  let q := Classical.choose (relativeSupportGlobalUnitFactor i F)
  have hq := Classical.choose_spec (relativeSupportGlobalUnitFactor i F)
  let η := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i.openComplement.ι).unit
  let H := ((CategoryTheory.evaluation _ _).obj F) ⋙
    relativeSupportEvaluation (Scheme.Etale.mk (𝟙 U))
  exact isKernelOfComp q.hom (H.map η)
    (KernelFork.mapIsLimit _ (kernelIsKernel η) H)
    (relativeSupportGlobalKernel_condition i F) hq

/-- The supported global functor equals evaluation of the supported sheaf at U.
Its inclusion equation fixes the identification, including at the empty scheme.
Source: Stacks Tag 09XP (blueprint: lem-pur-relative-support-bottom-descent).
Proof: global supported sections and evaluation of the sheaf support kernel are
both the kernel of F(U) -> F(U minus Z); use preservation of kernels by evaluation. -/
theorem relativeSupportGlobalIso_existsUnique {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] :
    ∃! e : supportSections i ≅
      relativeSupportKernel i ⋙ relativeSupportEvaluation (Scheme.Etale.mk (𝟙 U)),
      ∀ F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1},
        e.hom.app F ≫
          (relativeSupportEvaluation (Scheme.Etale.mk (𝟙 U))).map
            ((kernel.ι (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
              i.openComplement.ι).unit).app F) =
          kernel.ι (F.obj.map (supportRestrictionArrow i).op) := by
  let K := relativeSupportKernel i ⋙ relativeSupportEvaluation (Scheme.Etale.mk (𝟙 U))
  let ι : K ⟶ relativeSupportEvaluation (Scheme.Etale.mk (𝟙 U)) :=
    Functor.whiskerRight (kernel.ι
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i.openComplement.ι).unit)
        (relativeSupportEvaluation (Scheme.Etale.mk (𝟙 U)))
  let e : supportSections i ≅ K := NatIso.ofComponents
    (fun F ↦ (kernelIsKernel (F.obj.map (supportRestrictionArrow i).op)).conePointUniqueUpToIso
      (relativeSupportGlobalKernelLimit i F))
    (by
      intro F G a
      apply (cancel_mono (ι.app G)).1
      simp only [Category.assoc]
      have hF := (kernelIsKernel (F.obj.map (supportRestrictionArrow i).op))
        |>.conePointUniqueUpToIso_hom_comp
        (relativeSupportGlobalKernelLimit i F)
          WalkingParallelPair.zero
      have hG := (kernelIsKernel (G.obj.map (supportRestrictionArrow i).op))
        |>.conePointUniqueUpToIso_hom_comp
        (relativeSupportGlobalKernelLimit i G)
          WalkingParallelPair.zero
      change (supportSections i).map a ≫ _ ≫ ι.app G = _ ≫ K.map a ≫ ι.app G
      rw [show K.map a ≫ ι.app G = ι.app F ≫ _ from ι.naturality a,
        ← Category.assoc _ (ι.app F)]
      dsimp only [KernelFork.ofι, Fork.ofι_π_app] at hF hG
      rw [show _ ≫ ι.app G = _ from hG, show _ ≫ ι.app F = _ from hF]
      exact kernel.lift_ι _ _ _)
  have he : ∀ F, e.hom.app F ≫ ι.app F =
      kernel.ι (F.obj.map (supportRestrictionArrow i).op) := by
    intro F
    exact (kernelIsKernel (F.obj.map (supportRestrictionArrow i).op))
        |>.conePointUniqueUpToIso_hom_comp
      (relativeSupportGlobalKernelLimit i F)
        WalkingParallelPair.zero
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext F
  apply (cancel_mono (ι.app F)).1
  exact (he' F).trans (he F).symm

/-- The unique kernel-normalized global supported-sections identification.
Source: Stacks Tag 09XP (blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportGlobalIso {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] :=
  Classical.choose (relativeSupportGlobalIso_existsUnique i)

/-- Derivation preserves the global kernel identification.
Source: Stacks Tag 015N (blueprint: lem-pur-relative-support-bottom-descent).
Proof: derive the inverse natural transformations; functoriality makes their
composites the identity in each degree. -/
@[instance] theorem relativeSupportGlobalDerived_isIso {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (n : ℕ) :
    IsIso (NatTrans.rightDerived (relativeSupportGlobalIso i).hom n) := by
  let e := relativeSupportGlobalIso i
  refine ⟨⟨NatTrans.rightDerived e.inv n, ?_, ?_⟩⟩
  · rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  · rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

/-- Restriction of an actual global supported class to an etale object W.
Source: Stacks Tag 09XP (blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportGlobalRestriction
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (n : ℕ) {W : U.Etale}
    (a : W ⟶ Scheme.Etale.mk (𝟙 U)) :
    supportCohomology i n (relativeSupportCoefficient P U r) ⟶
      supportCohomology (pullback.snd i W.hom) n
        ((relativeSupportRestriction W).obj (relativeSupportCoefficient P U r)) :=
  (NatTrans.rightDerived (relativeSupportGlobalIso i).hom n).app
      (relativeSupportCoefficient P U r) ≫
    (NatTrans.rightDerived
      (Functor.whiskerLeft (relativeSupportKernel i) (relativeSupportEvaluationMap a)) n).app
        (relativeSupportCoefficient P U r) ≫
    (relativeSupportDerivedEvaluation i W n).app (relativeSupportCoefficient P U r)

/-- The finite signed module coefficient before forgetting its scalar action.
Source: the signed finite Tate sheaf of the coefficient conventions
(blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportModuleCoefficient
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) (r : ℤ) :=
  Scheme.finiteEtaleTateSheaf P.Coefficient (ringChar P.Coefficient) T
    (CharP.cast_eq_zero P.Coefficient (ringChar P.Coefficient)) r

/-- Naturality of Mathlib's kernel-preservation isomorphism for the support arrow.
Source: Stacks Tag 09XP (blueprint: lem-pur-relative-support-bottom-descent).
Proof: compose with the target kernel inclusion. Both composites are scalar
forgetting of the same section map, by kernel functoriality. Cancel the inclusion. -/
theorem relativeSupportForgetIso_naturality (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)} (a : F ⟶ G) :
    (ProEtale.etaleSupportKernel A i ⋙
        forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).map a ≫
      (PreservesKernel.iso (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
        (G.obj.map (supportRestrictionArrow i).op)).hom =
    (PreservesKernel.iso (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
        (F.obj.map (supportRestrictionArrow i).op)).hom ≫
      (moduleAbelianForget A T ⋙ supportSections i).map a := by
  simp only [Functor.comp_map, PreservesKernel.iso_hom]
  exact (kernelComparison_comp_kernel_map
    (F.obj.map (supportRestrictionArrow i).op)
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
    (G.obj.map (supportRestrictionArrow i).op)
    (a.hom.app (op (Scheme.Etale.mk (𝟙 T))))
    (a.hom.app (op (Scheme.Etale.mk i.openComplement.ι)))
    (a.hom.naturality (supportRestrictionArrow i).op)).symm

/-- Scalar forgetting of support kernels, using Mathlib's actual kernel-preservation
isomorphism. Its inclusion normalization is built into PreservesKernel.iso.
Source: Stacks Tag 09XP (blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportForgetIso (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    ProEtale.etaleSupportKernel A i ⋙
        forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1} ≅
      moduleAbelianForget A T ⋙ supportSections i :=
  NatIso.ofComponents
    (fun F ↦ PreservesKernel.iso
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
      (F.obj.map (supportRestrictionArrow i).op))
    (relativeSupportForgetIso_naturality A i)

/-- Scalar forgetting preserves finite colimits in the coefficient universe.
Source: Mathlib ModuleCat.forget₂PreservesColimitsOfSize and Stacks 03FD
(blueprint: lem-pur-relative-support-bottom-descent).
Proof: colimits of modules and abelian groups have the same underlying additive
presentation; specialize the existing colimit-preservation theorem to finite diagrams. -/
@[instance] theorem relativeSupportModuleForget_colimits
    (A : Type (u + 1)) [CommRing A] :
    PreservesFiniteColimits
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) := by
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} A
  infer_instance

/-- Derive the scalar-forgetting support comparison by the canonical base-change map.
Source: Stacks Tags 09XP and 015N
(blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportForgetDerived (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] (n : ℕ) :
    (ProEtale.etaleSupportKernel A i).rightDerived n ⋙
        forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1} ⟶
      moduleAbelianForget A T ⋙ (supportSections i).rightDerived n :=
  @Functor.rightDerivedBaseChange.{u + 1, u + 2, u + 1, u + 2,
    u + 1, u + 2, u + 1, u + 2, u + 1, u + 1, u + 1, u + 1}
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}
    _ _ _ _ _ _ _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
    _ _
    (ProEtale.etaleSupportKernel A i) (supportSections i) (moduleAbelianForget A T)
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
    _ _ _ _ _ _ _ _ (relativeSupportForgetIso A i).hom n

private theorem relativeSupportRestrictionArrow_mono {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] : Mono (supportRestrictionArrow i) := by
  apply (Scheme.Etale.forget T ⋙ Over.forget T).mono_of_mono_map
  change Mono i.openComplement.ι
  infer_instance

private theorem relativeSupportForget_acyclic (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (I : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) [Injective I] :
    (supportSections i).rightAcyclic ((moduleAbelianForget A T).obj I) := by
  have := relativeSupportRestrictionArrow_mono i
  let F := relativeSupportEvaluation (Scheme.Etale.mk (𝟙 T))
  let G := relativeSupportEvaluation (Scheme.Etale.mk i.openComplement.ι)
  let a := Sheaf.supportedSectionsInclusion T.smallEtaleTopology
    AddCommGrpCat.{u + 1} (supportRestrictionArrow i)
  let r := relativeSupportEvaluationMap (supportRestrictionArrow i)
  have hsurj (J : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective J] :
      Function.Surjective (r.app J) := by
    have : IsSplitEpi (J.obj.map (supportRestrictionArrow i).op) :=
      Sheaf.isSplitEpi_map_of_injective (supportRestrictionArrow i) J
    change Function.Surjective (J.obj.map (supportRestrictionArrow i).op)
    exact (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨δ, hδ⟩ := rightDerived_injective_sequence (supportSections i) F G a r
    (fun J _ ↦ (AddCommGrpCat.mono_iff_injective _).mp
      (show Mono (kernel.ι (J.obj.map (supportRestrictionArrow i).op)) from inferInstance))
    (fun J _ ↦ (ShortComplex.ab_exact_iff_function_exact _).mp
      (ShortComplex.exact_kernel (J.obj.map (supportRestrictionArrow i).op)))
    (fun J hJ ↦ by have := hJ; exact hsurj J)
  let M := (moduleAbelianForget A T).obj I
  have : IsSplitEpi (I.obj.map (supportRestrictionArrow i).op) :=
    Sheaf.isSplitEpi_map_of_injective (supportRestrictionArrow i) I
  have : Epi (r.app M) := by
    change Epi ((forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).map
      (I.obj.map (supportRestrictionArrow i).op))
    infer_instance
  have hepi : Epi ((r.rightDerived 0).app M) := by
    have : Epi (F.toRightDerivedZero.app M ≫ (r.rightDerived 0).app M) := by
      rw [rightDerived_zero_transformation]
      infer_instance
    exact epi_of_epi (F.toRightDerivedZero.app M) _
  intro n
  have hx0 (x : ((supportSections i).rightDerived (n + 1)).obj M) : x = 0 := by
    have hx : (a.rightDerived (n + 1)).app M x = 0 :=
      (AddCommGrpCat.subsingleton_of_isZero
        (moduleAbelianForget_injective_evaluation_acyclic A T I _ n)).elim _ _
    obtain ⟨y, hy⟩ := (hδ M n).2.2 x |>.mp hx
    rw [← hy]
    cases n with
    | zero =>
      obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective _).mp hepi y
      exact (hδ M 0).2.1.apply_apply_eq_zero z
    | succ n =>
      have hy0 : y = 0 :=
        (AddCommGrpCat.subsingleton_of_isZero
          (moduleAbelianForget_injective_evaluation_acyclic A T I _ n)).elim _ _
      rw [hy0, map_zero]
  have : Subsingleton (((supportSections i).rightDerived (n + 1)).obj M) :=
    ⟨fun x y ↦ (hx0 x).trans (hx0 y).symm⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- Scalar forgetting computes the same supported cohomology.
Source: Stacks Tags 09XP and 09XQ
(blueprint: lem-pur-relative-support-bottom-descent).
Proof: an injective module sheaf is flabby, its underlying abelian sheaf is flabby,
and flabby sheaves are acyclic for sections with closed support. Thus an injective
module resolution computes abelian supported cohomology. The termwise kernel
identification computes precisely the canonical base-change map above. -/
@[instance] theorem relativeSupportForgetDerived_isIso (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] (n : ℕ) :
    IsIso (relativeSupportForgetDerived A i n) := by
  have := relativeSupportSections_limits i
  let : HasDerivedCategory.{u + 1}
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _
  let : HasDerivedCategory.{u + 1}
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} A) :=
    HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _
  let : HasDerivedCategory.{u + 1} AddCommGrpCat.{u + 1} :=
    HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _
  have : IsIso (Functor.rightDerivedFunctorPlusBaseChange.{u + 1, u + 2, u + 1,
      u + 2, u + 1, u + 2, u + 1, u + 2, u + 1, u + 1, u + 1, u + 1}
      (relativeSupportForgetIso A i).hom) :=
    Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
      (relativeSupportForgetIso A i) (fun I _ ↦ relativeSupportForget_acyclic A i I)
  change IsIso (Functor.rightDerivedBaseChange.{u + 1, u + 2, u + 1, u + 2,
    u + 1, u + 2, u + 1, u + 2, u + 1, u + 1, u + 1, u + 1}
    (relativeSupportForgetIso A i).hom n)
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  rw [Functor.rightDerivedBaseChange_app]
  infer_instance

/-- The canonical supported etale/pro-etale comparison, including scalar forgetting.
It derives the published comparison unit, normalized by the adjunction unit on
ordinary sections; thus it is not an arbitrary group isomorphism.
Source: Stacks Tags 099V, 099W and 09XP
(blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportProComparison (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] (n : ℕ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    supportCohomology i n ((moduleAbelianForget A T).obj F) ⟶
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).obj
        (ProEtale.supportCohomology i A n
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F)) :=
  (asIso (relativeSupportForgetDerived A i n)).inv.app F ≫
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).map
      ((Functor.rightDerivedBaseChange
        (β := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T)
        (γ := 𝟭 (ModuleCat.{u + 1} A))
        ((Functor.rightUnitor _).hom ≫ ProEtale.supportComparisonUnit A i) n).app F)

private theorem relativeSupportProSections_limits (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    PreservesFiniteLimits (ProEtale.supportSections i A) := by
  let F := ProEtale.sectionsFunctor (ModuleCat.{u + 1} A)
    ((Scheme.toProEt T).obj (Scheme.Etale.mk (𝟙 T)))
  let G := ProEtale.sectionsFunctor (ModuleCat.{u + 1} A)
    ((Scheme.toProEt T).obj (Scheme.Etale.mk i.openComplement.ι))
  let r : F ⟶ G := Functor.whiskerLeft
    (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
    ((CategoryTheory.evaluation _ _).map (ProEtale.supportRestrictionArrow i).op)
  let ι : ProEtale.supportSections i A ⟶ F :=
    { app := fun M ↦ kernel.ι (r.app M)
      naturality := by intro M N f; exact kernel.lift_ι _ _ _ }
  have : ∀ M, Mono (ι.app M) := fun M ↦ by dsimp [ι]; infer_instance
  exact ModuleRestrictionKernel.kernelLeftExact F G (ProEtale.supportSections i A) r ι
    (fun M ↦ kernel.condition _) (fun M ↦ kernelIsKernel _)

private theorem relativeSupportPro_acyclic (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (I : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) [Injective I] :
    (ProEtale.supportSections i A).rightAcyclic
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj I) := by
  let C := ModuleCat.{u + 1} A
  let L := ProEtale.comparisonLowerStar C T
  let B := ProEtale.comparisonUpperStar C T
  let G := ProEtale.etaleSupportKernel A i
  let G' := ProEtale.supportSections i A
  have := ProEtale.isIso_comparisonAdjunction_unit C T
  have : L.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (ProEtale.comparisonAdjunction C T)
  let eG : L ⋙ G ≅ G' := Iso.refl _
  have hu := (ProEtale.comparisonAdjunction C T).isIso_derivedPlus_unit_app_of_rightAcyclic
    (fun _ _ ↦ inferInstance)
    (fun J _ ↦ ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective C T J)
    ((DerivedCategory.Plus.singleFunctor _ 0).obj I)
  intro n
  let q := n + 1
  let eR : (L ⋙ G).rightDerived q ≅ G'.rightDerived q :=
    { hom := NatTrans.rightDerived eG.hom q
      inv := NatTrans.rightDerived eG.inv q
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, eG.hom_inv_id,
        NatTrans.rightDerived_id]
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, eG.inv_hom_id,
        NatTrans.rightDerived_id] }
  let e : (DerivedCategory.Plus.singleFunctor _ 0 ⋙
      (L ⋙ G).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C q).obj
        (B.obj I) ≅
      (DerivedCategory.Plus.singleFunctor _ 0 ⋙ G.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor C q).obj I :=
    (DerivedCategory.Plus.homologyFunctor C q).mapIso
      ((Functor.rightDerivedFunctorPlusCompIso L G).app _ ≪≫
        G.rightDerivedFunctorPlus.mapIso
          (L.rightDerivedFunctorPlus.mapIso
            (((B.mapDerivedCategoryPlusSingleFunctor 0).app I).symm) ≪≫
          (asIso ((ProEtale.comparisonAdjunction C T).derivedPlus.unit.app _)).symm))
  let e' := eR.symm.app _ ≪≫
    ((L ⋙ G).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q).symm.app _ ≪≫
    e ≪≫ (G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q).app I
  exact (Functor.isZero_rightDerived_obj_injective_succ G n I).of_iso e'

private theorem relativeSupportProUnit_isIso (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    IsIso (ProEtale.supportComparisonUnit A i) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  let η := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F
  have := ProEtale.isIso_comparisonAdjunction_unit (ModuleCat.{u + 1} A) T
  let e := kernel.mapIso (F.obj.map (supportRestrictionArrow i).op)
    (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F).obj.map
      (ProEtale.supportRestrictionArrow i).op)
    (asIso (η.hom.app (op (Scheme.Etale.mk (𝟙 T)))))
    (asIso (η.hom.app (op (Scheme.Etale.mk i.openComplement.ι))))
    (η.hom.naturality (supportRestrictionArrow i).op)
  have he : (ProEtale.supportComparisonUnit A i).app F = e.hom := by
    apply (cancel_mono (kernel.ι
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F).obj.map
        (ProEtale.supportRestrictionArrow i).op))).1
    exact ((Classical.choose_spec
      (ProEtale.supportComparisonUnit_existsUnique A i)).1 F).trans
        (kernel.lift_ι _ _ _).symm
  rw [he]
  infer_instance

/-- Finite-coefficient support comparison is invertible for an arbitrary scheme.
Source: Stacks Tags 099V, 099W and 09XP
(blueprint: lem-pur-relative-support-bottom-descent).
Proof: comparison direct image preserves injectives and its composite with the
etale support kernel is the pro-etale support kernel. The derived comparison unit
identifies their derived values on comparison pullbacks. Thus pulled-back injectives
are support-acyclic. The ordinary unit comparison is invertible by preservation of
kernels, and the canonical derived base change is invertible by this acyclicity.
No finite-type, separatedness or Noetherian assumption enters the argument. -/
@[instance] theorem relativeSupportProComparison_isIso (A : Type (u + 1)) [CommRing A]
    [Finite A] {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] (n : ℕ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    IsIso (relativeSupportProComparison A i n F) := by
  have := relativeSupportProSections_limits A i
  have := relativeSupportProUnit_isIso A i
  let e := (Functor.rightUnitor (ProEtale.etaleSupportKernel A i)).hom ≫
    ProEtale.supportComparisonUnit A i
  have : IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (β := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T)
      (γ := 𝟭 (ModuleCat.{u + 1} A)) e) :=
    Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
      (asIso e) (fun I _ ↦ relativeSupportPro_acyclic A i I)
  unfold relativeSupportProComparison
  have : IsIso ((Functor.rightDerivedBaseChange
      (β := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T)
      (γ := 𝟭 (ModuleCat.{u + 1} A)) e n).app F) := by
    rw [Functor.rightDerivedBaseChange_app]
    infer_instance
  infer_instance

/-- The coefficient on W is the restriction of the same signed coefficient on U.
Source: Stacks Tag 03F3 (blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportModuleRestriction
    (P : WeilConjectures.PurityFiniteSetting.{u}) {U : Scheme.{u}} (W : U.Etale) (r : ℤ) :=
  (localizationRestriction (ModuleCat.{u + 1} P.Coefficient) W.hom inferInstance).obj
    (relativeSupportModuleCoefficient P U r)

/-- The pro-etale edge to the same restricted cohomology sheaf on U, transported
through the canonical, unit-induced support comparison.
Source: Stacks Tags 099W and 09XP
(blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportProEdge
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (n : ℕ) (W : U.Etale) :=
  (asIso (relativeSupportProComparison P.Coefficient (pullback.snd i W.hom) n
    (relativeSupportModuleRestriction P W r))).inv ≫ relativeSupportEdge P i r n W

/-- On coefficients of etale origin, canonical support comparison transports etale
restriction to pro-etale restriction. This supplies restriction without a second
choice of resolutions on the two sites.
Source: Stacks Tags 099W and 09XP
(blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportProRestriction
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (n : ℕ) {W W' : U.Etale}
    (a : W' ⟶ W) :=
  (asIso (relativeSupportProComparison P.Coefficient (pullback.snd i W.hom) n
    (relativeSupportModuleRestriction P W r))).inv ≫
    relativeSupportClassRestriction P i r n a ≫
    relativeSupportProComparison P.Coefficient (pullback.snd i W'.hom) n
      (relativeSupportModuleRestriction P W' r)

/-- Descent in the bottom supported degree of a smooth pair.
Source: Stacks Tag 09XP, section-cohomology-support, Tags 09XQ, 015N and 0FUE;
main-20261015, sec-smooth-purity/sk-prop-an/lem-pur-frame-independence.proof.md.
(blueprint: lem-pur-relative-support-bottom-descent).

Proof:
1. For c=0 the empty frame cuts out all of U. The support functor is identity,
   so its negative cohomology vanishes and its degree-zero edge is identity.
2. For c>0 use lem-pur-smooth-pair-local-coordinates and pull its chart back to U.
   Etale restriction is exact and preserves injectives, hence commutes with the derived
   support kernel. Apply lem-pur-relative-support-coordinate-model at each supported
   geometric point. The codimension equation at every point of Z gives normal rank c.
3. On the resulting affine-space model over the fixed algebraically closed field k,
   thm-pur-rank-one-local-calculation and lem-pur-kunneth-supported identify the complex
   with A[-2c]. The twists are locally free rank one, including the negative dual twists;
   free shifted factors introduce no negative Tor. By lem-kun-stalks-of-cohomology the
   supported stalks vanish below 2c. Off the support the kernel is locally zero.
   Geometric-stalk conservativity gives the asserted sheaf vanishing.
4. The closed-support adjunction of lem-pur-etale-supported-kernel-adjunction expresses
   P_Z as i_* i^!_0. Exact i_* and both right adjoints preserve injectives, so P_Z sends
   injectives to injectives. Evaluation at W is thus acyclic on P_Z of injectives.
5. Etale restriction preserves injectives. Its ordinary kernel comparison identifies
   R^n(P_Z followed by evaluation at W) with the recorded supported cohomology on W.
   Apply thm-sp-grothendieck to P_Z and evaluation at W on the fixed site of U.
6. Vanishing of rows q<2c leaves just (0,2c) in total degree 2c. The finite abutment
   filtration and lem-pur-first-quadrant-lowest-row-edge make the canonical edge invertible.
   This is the filtration edge of lem-sp-grothendieck-edge-maps.
   The natural-number/integer comparison identifies its target with the stated sheaf.
7. On one injective resolution on U, lem-pc-grothendieck-edge-cocycle identifies the edge
   with the cycles-to-cohomology map. This is a morphism of sheaves, so the square for
   every further etale restriction commutes. The kernel-normalized transports above
   give precisely the recorded W-side groups, not unrelated local cohomology sheaves.
8. Direct image along the site comparison preserves injectives and its composite with
   the etale support kernel is literally the pro-etale support kernel. The invertible
   derived comparison unit therefore identifies derived support after comparison
   pullback with etale derived support. The underived map is normalized by the
   adjunction unit on sections. It is an isomorphism by the kernel universal property;
   acyclicity on pulled-back injectives makes its canonical derived base change an
   isomorphism too. Scalar forgetting has the same kernel normalization and is derived
   using evaluation acyclicity and the support restriction long exact sequence.
9. If supported classes agree on a covering family, the natural edge maps give sections
   of the same cohomology sheaf that agree on that cover. Sheaf separation identifies
   the sections and the invertible global edge identifies the original classes.
   Empty coverings of the empty scheme and c=0 are included. No orientation is used. -/
theorem relative_support_bottom_descent
    (P : WeilConjectures.PurityFiniteSetting.{u}) (c d : ℕ)
    {B V Z U : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) (v : V ⟶ B)
    [SmoothOfRelativeDimension d v] (i : Z ⟶ V) [IsClosedImmersion i]
    [Smooth (i ≫ v)]
    (hcodim : ∀ z : Z,
      ringKrullDim (V.presheaf.stalk (i.base z)) =
        ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞))
    (e : U ⟶ V) [Etale e]
    (f : Fin c → Γ(U, ⊤))
    (toZ : U.zeroLocusSubscheme (Set.range f) ⟶ Z)
    (hframe : IsPullback toZ (U.zeroLocusSubschemeι (Set.range f)) i e)
    (r : ℤ) :
    (∀ b' : ℤ, b' < 2 * (c : ℤ) →
      IsZero (relativeSupportCohomologySheaf P (pullback.snd i e) r b')) ∧
    (∀ W : U.Etale, IsIso (relativeSupportEdge P (pullback.snd i e) r (2 * c) W)) ∧
    (∀ (W W' : U.Etale) (a : W' ⟶ W),
      relativeSupportClassRestriction P (pullback.snd i e) r (2 * c) a ≫
          relativeSupportEdge P (pullback.snd i e) r (2 * c) W' =
        relativeSupportEdge P (pullback.snd i e) r (2 * c) W ≫
          (relativeSupportCohomologySheaf P (pullback.snd i e) r ((2 * c : ℕ) : ℤ)).obj.map a.op) ∧
    (∀ W : U.Etale,
      IsIso (relativeSupportProComparison P.Coefficient
        (pullback.snd (pullback.snd i e) W.hom) (2 * c)
        (relativeSupportModuleRestriction P W r)) ∧
      IsIso (relativeSupportProEdge P (pullback.snd i e) r (2 * c) W)) ∧
    (∀ (W W' : U.Etale) (a : W' ⟶ W),
      relativeSupportProRestriction P (pullback.snd i e) r (2 * c) a ≫
          relativeSupportProEdge P (pullback.snd i e) r (2 * c) W' =
        relativeSupportProEdge P (pullback.snd i e) r (2 * c) W ≫
          (relativeSupportCohomologySheaf P (pullback.snd i e) r ((2 * c : ℕ) : ℤ)).obj.map a.op) ∧
    (∀ (ι : Type w) (W : ι → U.Etale)
      (a : ∀ t : ι, W t ⟶ Scheme.Etale.mk (𝟙 U)),
      Sieve.ofArrows W a ∈ U.smallEtaleTopology (Scheme.Etale.mk (𝟙 U)) →
      ∀ x y : supportCohomology (pullback.snd i e) (2 * c)
        (relativeSupportCoefficient P U r),
      (∀ t : ι,
        relativeSupportGlobalRestriction P (pullback.snd i e) r (2 * c) (a t) x =
          relativeSupportGlobalRestriction P (pullback.snd i e) r (2 * c) (a t) y) →
      x = y) := by
  sorry

end AlgebraicGeometry.Etale
