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

import Sheaf.AlgebraicGeometry.ModuleCohomologyConventions
import WeilConjectures.CategoryTheory.RightDerivedInjectiveSequence
import WeilConjectures.CategoryTheory.RightDerivedZeroTransformation
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.CategoryTheory.Sites.SectionsWithSupport
import all Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction
import all Sheaf.CategoryTheory.ModuleRestrictionKernelComparison
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.CategoryTheory.GrothendieckEdgeCocycle
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.RelativeSupportVanishing

/-! # Descent in the bottom supported degree of a smooth pair

Source: Stacks Project, Tag 09XP, section-cohomology-support; the relative smooth-pair
refinement in the blueprint (blueprint: lem-pur-relative-support-bottom-descent).

The support cohomology sheaf is formed on the fixed site of U by deriving the actual
closed-support kernel. Kernel-normalized comparison identifies its evaluation-derived
functors with the recorded supported-cohomology groups on etale objects. The edge is
natural in these objects. The pro-etale comparison derives the published adjunction-unit
map on support kernels, and descent tests global supported classes on an arbitrary cover.

The canonical support, evaluation, scalar-forgetting and site-comparison interfaces
are proved below. The final theorem derives the bottom edge, its restriction squares
and descent from the separate smooth-pair lower-vanishing theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v v' w

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
    (i : Z ⟶ U) [IsClosedImmersion i] (W : U.Etale) :
    relativeSupportKernel i ⋙ relativeSupportEvaluation W ≅
      relativeSupportRestriction W ⋙ supportSections (pullback.snd i W.hom) :=
  Classical.choose (relativeSupportEvaluationIso_existsUnique i W)

attribute [local irreducible] relativeSupportKernel

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
    (i : Z ⟶ U) [IsClosedImmersion i] (W : U.Etale) (n : ℕ) :
    (relativeSupportKernel i ⋙ relativeSupportEvaluation W).rightDerived n ⋙
        𝟭 AddCommGrpCat.{u + 1} ⟶
      relativeSupportRestriction W ⋙ (supportSections (pullback.snd i W.hom)).rightDerived n :=
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

/-- Invertibility of derived base change, proved once before specializing the
categories to scheme-dependent sheaf categories. It follows termwise from the
canonical base-change formula and invertibility of the derived-plus comparison. -/
private theorem relativeSupportDerivedBaseChange_isIso
    {B B' C C' : Type (u + 2)}
    [Category.{u + 1} B] [Category.{u + 1} B']
    [Category.{u + 1} C] [Category.{u + 1} C']
    [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
    [HasDerivedCategory B] [HasDerivedCategory B']
    [HasDerivedCategory C] [HasDerivedCategory C']
    [EnoughInjectives B] [EnoughInjectives B']
    {G : B ⥤ C} {G' : B' ⥤ C'} {β : B ⥤ B'} {γ : C ⥤ C'}
    [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
    [PreservesFiniteLimits β] [PreservesFiniteColimits β]
    [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]
    (e : G ⋙ γ ⟶ β ⋙ G')
    [IsIso (Functor.rightDerivedFunctorPlusBaseChange e)] (n : ℕ) :
    IsIso (Functor.rightDerivedBaseChange e n) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  rw [Functor.rightDerivedBaseChange_app]
  infer_instance

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
  exact relativeSupportDerivedBaseChange_isIso
    (β := β) (γ := 𝟭 AddCommGrpCat.{u + 1}) e.hom n

attribute [local irreducible] relativeSupportDerivedEvaluation relativeSupportEvaluationIso

/-- The canonical natural-number/integer derived cohomology comparison, with the
recorded support cohomology sheaf as its explicit target. Naming this isomorphism
keeps evaluation and naturality proofs from unfolding the cohomology object.
Source: the canonical single/right-derived-plus/homology comparison, Stacks 09XP
(blueprint: lem-pur-relative-support-bottom-descent). -/
@[irreducible] noncomputable def relativeSupportCohomologyIso
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (n : ℕ) :
    ((relativeSupportKernel i).rightDerived n).obj (relativeSupportCoefficient P U r) ≅
      relativeSupportCohomologySheaf P i r n :=
  ((relativeSupportKernel i).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
    n).symm.app (relativeSupportCoefficient P U r)

attribute [local irreducible] relativeSupportCohomologySheaf

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
      (relativeSupportCohomologyIso P i r n).hom

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

attribute [local semireducible] relativeSupportKernel

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

attribute [local irreducible] relativeSupportKernel

/-- The unique kernel-normalized global supported-sections identification.
Source: Stacks Tag 09XP (blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportGlobalIso {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] :
    supportSections i ≅
      relativeSupportKernel i ⋙ relativeSupportEvaluation (Scheme.Etale.mk (𝟙 U)) :=
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

attribute [local irreducible] relativeSupportGlobalIso

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
        ((module_cohomology_conventions A T).1 I _ (n + 1) (Nat.succ_pos n))).elim _ _
    obtain ⟨y, hy⟩ := (hδ M n).2.2 x |>.mp hx
    rw [← hy]
    cases n with
    | zero =>
      obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective _).mp hepi y
      exact (hδ M 0).2.1.apply_apply_eq_zero z
    | succ n =>
      have hy0 : y = 0 :=
        (AddCommGrpCat.subsingleton_of_isZero
          ((module_cohomology_conventions A T).1 I _ (n + 1) (Nat.succ_pos n))).elim _ _
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
  exact relativeSupportDerivedBaseChange_isIso
    (β := moduleAbelianForget A T)
    (γ := forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
    (relativeSupportForgetIso A i).hom n

attribute [local irreducible] relativeSupportForgetDerived

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
    have : IsIso (Functor.rightDerivedBaseChange
        (β := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T)
        (γ := 𝟭 (ModuleCat.{u + 1} A)) e n) :=
      relativeSupportDerivedBaseChange_isIso e n
    infer_instance
  infer_instance

attribute [local irreducible] relativeSupportProComparison

/-- The coefficient on W is the restriction of the same signed coefficient on U.
Source: Stacks Tag 03F3 (blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportModuleRestriction
    (P : WeilConjectures.PurityFiniteSetting.{u}) {U : Scheme.{u}} (W : U.Etale) (r : ℤ) :
    Sheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient) :=
  (localizationRestriction (ModuleCat.{u + 1} P.Coefficient) W.hom inferInstance).obj
    (relativeSupportModuleCoefficient P U r)

/-- Scalar forgetting and etale localization give the same underlying coefficient.
This reflexive isomorphism records the coefficient identification before deriving it.
Source: the sectionwise definitions of localizationRestriction and sheafCompose
(blueprint: lem-pur-relative-support-bottom-descent). -/
@[irreducible] noncomputable def relativeSupportRestrictionCoefficientIso
    (P : WeilConjectures.PurityFiniteSetting.{u}) {U : Scheme.{u}} (W : U.Etale) (r : ℤ) :
    (moduleAbelianForget P.Coefficient W.left).obj (relativeSupportModuleRestriction P W r) ≅
      (relativeSupportRestriction W).obj (relativeSupportCoefficient P U r) :=
  Iso.refl _

/-- The canonical pro-etale comparison with the recorded restricted abelian coefficient.
Derive the reflexive coefficient identification before composing comparison maps, so
checking their types does not unfold the cohomology objects.
Source: the canonical supported comparison and exact scalar forgetting
(blueprint: lem-pur-relative-support-bottom-descent). -/
@[irreducible] noncomputable def relativeSupportProIso
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (n : ℕ) (W : U.Etale) :
    (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).obj
        (ProEtale.supportCohomology (pullback.snd i W.hom) P.Coefficient n
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) W.left).obj
            (relativeSupportModuleRestriction P W r))) ≅
      supportCohomology (pullback.snd i W.hom) n
        ((relativeSupportRestriction W).obj (relativeSupportCoefficient P U r)) :=
  (asIso (relativeSupportProComparison P.Coefficient (pullback.snd i W.hom) n
    (relativeSupportModuleRestriction P W r))).symm ≪≫
      ((supportSections (pullback.snd i W.hom)).rightDerived n).mapIso
        (relativeSupportRestrictionCoefficientIso P W r)

/-- The pro-etale edge to the same restricted cohomology sheaf on U, transported
through the canonical, unit-induced support comparison.
Source: Stacks Tags 099W and 09XP
(blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportProEdge
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (n : ℕ) (W : U.Etale) :
    (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).obj
        (ProEtale.supportCohomology (pullback.snd i W.hom) P.Coefficient n
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) W.left).obj
            (relativeSupportModuleRestriction P W r))) ⟶
      (relativeSupportCohomologySheaf P i r n).obj.obj (op W) :=
  (relativeSupportProIso P i r n W).hom ≫ relativeSupportEdge P i r n W

/-- On coefficients of etale origin, canonical support comparison transports etale
restriction to pro-etale restriction. This supplies restriction without a second
choice of resolutions on the two sites.
Source: Stacks Tags 099W and 09XP
(blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportProRestriction
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (n : ℕ) {W W' : U.Etale}
    (a : W' ⟶ W) :
    (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).obj
        (ProEtale.supportCohomology (pullback.snd i W.hom) P.Coefficient n
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) W.left).obj
            (relativeSupportModuleRestriction P W r))) ⟶
      (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).obj
        (ProEtale.supportCohomology (pullback.snd i W'.hom) P.Coefficient n
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) W'.left).obj
            (relativeSupportModuleRestriction P W' r))) :=
  (relativeSupportProIso P i r n W).hom ≫
    relativeSupportClassRestriction P i r n a ≫ (relativeSupportProIso P i r n W').inv

private theorem relativeSupportKernel_preservesFiniteLimits
    {Z U : Scheme.{u}} (i : Z ⟶ U) [IsClosedImmersion i] :
    PreservesFiniteLimits (relativeSupportKernel i) := by
  unfold relativeSupportKernel
  let j := i.openComplement.ι
  let K := sectionsWithSupport AddCommGrpCat.{u + 1} j
  let F := 𝟭 (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
  let G := upperStar AddCommGrpCat.{u + 1} j ⋙ lowerStar AddCommGrpCat.{u + 1} j
  let r : F ⟶ G := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).unit
  let ι : K ⟶ F := sectionsWithSupportι AddCommGrpCat.{u + 1} j
  have : ∀ X, Mono (ι.app X) := fun X ↦ by
    change Mono (kernel.ι (r.app X))
    infer_instance
  have hK : PreservesFiniteLimits K := ModuleRestrictionKernel.kernelLeftExact F G K r ι
    (fun X ↦ kernel.condition (r.app X)) (fun X ↦ kernelIsKernel (r.app X))
  exact preservesFiniteLimits_of_natIso (supportedKernelIso j).symm

private def relativeSupportKernelIso {Z U : Scheme.{u}} (i : Z ⟶ U)
    [IsClosedImmersion i] : relativeSupportKernel i ≅
      sectionsWithSupport AddCommGrpCat.{u + 1} i.openComplement.ι := by
  unfold relativeSupportKernel
  exact supportedKernelIso i.openComplement.ι

private theorem relativeSupportGrothendieckEdge_naturality
    {A B C : Type (u + 2)} [Category.{u + 1} A] [Category.{u + 1} B]
    [Category.{u + 1} C] [Abelian A] [Abelian B] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} A] [IsGrothendieckAbelian.{u + 1} B]
    [IsGrothendieckAbelian.{u + 1} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G G' : B ⥤ C) [F.Additive] [G.Additive] [G'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] [PreservesFiniteLimits G']
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics)
    (hFG' : (⟨F, G'⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics)
    (α : G ⟶ G') (X : A) (n : ℕ) :
    (NatTrans.rightDerived (Functor.whiskerLeft F α) n).app X ≫
        (F.grothendieckLeftEdgeMap G' hFG' n).app X =
      (F.grothendieckLeftEdgeMap G hFG n).app X ≫ α.app ((F.rightDerived n).obj X) := by
  let I := injectiveResolution X
  let K := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let T := ((F ⋙ G).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let T' := ((F ⋙ G').mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let τ : T ⟶ T' :=
    (NatTrans.mapHomologicalComplex (Functor.whiskerLeft F α) _).app I.cocomplex
  obtain ⟨c, hc, he⟩ := (grothendieck_left_edge_cocycle F G
    hFG X I).1 n
  obtain ⟨c', hc', he'⟩ := (grothendieck_left_edge_cocycle F G'
    hFG' X I).1 n
  have hciso : IsIso c := by
    have h : IsLimit (KernelFork.ofι (G.map (K.iCycles n))
        (show G.map (K.iCycles n) ≫ T.d n (n + 1) = 0 from by
          change G.map (K.iCycles n) ≫ G.map (K.d n (n + 1)) = 0
          rw [← G.map_comp, K.iCycles_d, G.map_zero])) :=
      KernelFork.mapIsLimit _ (K.cyclesIsKernel n (n + 1) (by simp)) G
    obtain ⟨d, hd⟩ := KernelFork.IsLimit.lift' h (T.iCycles n)
      (T.iCycles_d n (n + 1))
    change d ≫ G.map (K.iCycles n) = T.iCycles n at hd
    refine ⟨⟨d, ?_, ?_⟩⟩
    · apply (cancel_mono (G.map (K.iCycles n))).1
      erw [Category.assoc, hd, hc, Category.id_comp]
    · apply (cancel_mono (T.iCycles n)).1
      erw [Category.assoc, hc, hd, Category.id_comp]
  have hcyc : c ≫ HomologicalComplex.cyclesMap τ n = α.app (K.cycles n) ≫ c' := by
    apply (cancel_mono (T'.iCycles n)).1
    rw [Category.assoc, HomologicalComplex.cyclesMap_i,
      ← Category.assoc, hc, Category.assoc, hc']
    exact α.naturality (K.iCycles n)
  apply (cancel_epi ((I.isoRightDerivedObj (F ⋙ G) n).inv)).1
  apply (cancel_epi (T.homologyπ n)).1
  apply (cancel_epi c).1
  apply (cancel_mono (G'.map (I.isoRightDerivedObj F n).hom)).1
  simp only [Category.assoc]
  erw [I.rightDerived_app_eq]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  erw [HomologicalComplex.homologyπ_naturality_assoc τ n]
  rw [← Category.assoc c, hcyc]
  simp only [Category.assoc]
  erw [he', ← α.naturality (I.isoRightDerivedObj F n).hom]
  rw [reassoc_of% he]
  exact (α.naturality (K.homologyπ n)).symm

private theorem relativeSupportGrothendieckEdge_isIso
    {A B C : Type (u + 2)} [Category.{u + 1} A] [Category.{u + 1} B]
    [Category.{u + 1} C] [Abelian A] [Abelian B] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} A] [IsGrothendieckAbelian.{u + 1} B]
    [IsGrothendieckAbelian.{u + 1} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics)
    (X : A) (n : ℕ)
    (hq : ∀ q : ℕ, q < n → IsZero ((F.rightDerived q).obj X)) :
    IsIso ((F.grothendieckLeftEdgeMap G hFG n).app X) := by
  let Y := F.grothendieckSpectralObject G X
  have hinterval (m : ℕ) (a : ℕ) (ha : a ≤ n) :
      IsZero ((Y.H m).obj (ComposableArrows.mk₁
        (homOfLE (bot_le : (⊥ : EInt) ≤ (a : ℤ))))) := by
    induction a with
    | zero => exact Y.isZero₁_of_isFirstQuadrant _ _ _ le_rfl m
    | succ a ih =>
      apply (Y.exact₂ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : ℤ)))
        (homOfLE (show ((a : ℤ) : EInt) ≤ ((a + 1 : ℤ) : EInt) by simp))
        (homOfLE bot_le) (Subsingleton.elim _ _) m).isZero_of_both_isZero
      · exact ih (by omega)
      · have hm : IsZero (((G.rightDerived (m - a)).obj ((F.rightDerived a).obj X))) :=
          Functor.map_isZero _ (hq a (by omega))
        by_cases ham : a ≤ m
        · exact hm.of_iso ((F.grothendieckSpectralObjectHIso G (m - a) a m a
            (a + 1) (by omega) rfl rfl).app X)
        · exact Y.isZero₂_of_isFirstQuadrant _ _ _ m (by simp; omega)
  have := Y.isIso_H_map_twoδ₁Toδ₀' (n : ℤ) ((n : ℤ) + 1) rfl
    ⊥ ((n : ℤ) : EInt) ⊤ bot_le le_top (hinterval n n le_rfl)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hinterval (n + 1) n le_rfl)
  have := Y.isIso_H_map_self_succ_top n
  have : IsIso (Y.leftEdge n) := by
    dsimp [Abelian.SpectralObject.leftEdge]
    infer_instance
  change IsIso ((F.grothendieckSpectralObjectHBotTopIso G hFG n).inv.app X ≫
    Y.leftEdge n ≫ (F.grothendieckLeftEdgeTargetIso G n).hom.app X)
  infer_instance

private theorem relativeSupportEdge_isIso_of_vanishing
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (n : ℕ)
    (hz : ∀ q : ℕ, q < n → IsZero (relativeSupportCohomologySheaf P i r q))
    (W : U.Etale) : IsIso (relativeSupportEdge P i r n W) := by
  let F := relativeSupportKernel i
  have : PreservesFiniteLimits F := relativeSupportKernel_preservesFiniteLimits i
  let G := relativeSupportEvaluation W
  let X := relativeSupportCoefficient P U r
  have hq (q : ℕ) (hq : q < n) : IsZero ((F.rightDerived q).obj X) :=
    (hz q hq).of_iso
      (relativeSupportCohomologyIso P i r q)
  have : IsIso ((F.grothendieckLeftEdgeMap G
      (relativeSupport_evaluationAcyclic i W) n).app X) :=
    relativeSupportGrothendieckEdge_isIso F G (relativeSupport_evaluationAcyclic i W) X n hq
  unfold relativeSupportEdge
  infer_instance

private theorem relativeSupportTransportedEdge_naturality
    {C : Type (u + 2)} [Category.{u + 1} C]
    {S S' T T' H H' V V' : C} (d : T ≅ S) (d' : T' ≅ S')
    (a : T ⟶ T') (f : T ⟶ H) (f' : T' ⟶ H') (b : H ⟶ H')
    (t : H ⟶ V) (t' : H' ⟶ V') (k : V ⟶ V')
    (hf : a ≫ f' = f ≫ b) (ht : b ≫ t' = t ≫ k) :
    (d.inv ≫ a ≫ d'.hom) ≫ (d'.inv ≫ f' ≫ t') =
      (d.inv ≫ f ≫ t) ≫ k := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hf, ht]

set_option backward.isDefEq.respectTransparency false in
private theorem relativeSupportEdge_naturality
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (r : ℤ) (n : ℕ) {W W' : U.Etale}
    (a : W' ⟶ W) :
    relativeSupportClassRestriction P i r n a ≫ relativeSupportEdge P i r n W' =
      relativeSupportEdge P i r n W ≫
        (relativeSupportCohomologySheaf P i r n).obj.map a.op := by
  let F := relativeSupportKernel i
  have : PreservesFiniteLimits F := relativeSupportKernel_preservesFiniteLimits i
  let G := relativeSupportEvaluation W
  let G' := relativeSupportEvaluation W'
  let α : G ⟶ G' := relativeSupportEvaluationMap a
  let X := relativeSupportCoefficient P U r
  have hnat := relativeSupportGrothendieckEdge_naturality F G G'
    (relativeSupport_evaluationAcyclic i W) (relativeSupport_evaluationAcyclic i W') α X n
  exact relativeSupportTransportedEdge_naturality
    ((asIso (relativeSupportDerivedEvaluation i W n)).app X)
    ((asIso (relativeSupportDerivedEvaluation i W' n)).app X)
    ((NatTrans.rightDerived (Functor.whiskerLeft F α) n).app X)
    ((F.grothendieckLeftEdgeMap G (relativeSupport_evaluationAcyclic i W) n).app X)
    ((F.grothendieckLeftEdgeMap G' (relativeSupport_evaluationAcyclic i W') n).app X)
    (α.app ((F.rightDerived n).obj X))
    (G.map (relativeSupportCohomologyIso P i r n).hom)
    (G'.map (relativeSupportCohomologyIso P i r n).hom)
    _ hnat (α.naturality
      (relativeSupportCohomologyIso P i r n).hom).symm


private theorem relativeSupportSeparatedCover
    {C : Type v} [Category.{v'} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget AddCommGrpCat.{u + 1})]
    (F : Sheaf J AddCommGrpCat.{u + 1}) (X : C) (M : AddCommGrpCat.{u + 1})
    (m : M ⟶ F.obj.obj (op X)) [IsIso m]
    {ι : Type w} (W : ι → C) (a : ∀ t, W t ⟶ X)
    (hcover : Sieve.ofArrows W a ∈ J X) (N : ι → AddCommGrpCat.{u + 1})
    (restriction : ∀ t, M ⟶ N t) (edge : ∀ t, N t ⟶ F.obj.obj (op (W t)))
    (hres : ∀ t, m ≫ F.obj.map (a t).op = restriction t ≫ edge t)
    (x y : M) (hxy : ∀ t, restriction t x = restriction t y) : x = y := by
  apply (ConcreteCategory.bijective_of_isIso m).1
  apply F.isSeparated X (Sieve.ofArrows W a) hcover
  intro T t ht
  obtain ⟨s, a', rfl⟩ := (Sieve.mem_ofArrows_iff W a t).mp ht
  change (F.obj.map (a' ≫ a s).op) (m x) = (F.obj.map (a' ≫ a s).op) (m y)
  simp only [op_comp, Functor.map_comp, AddCommGrpCat.comp_apply]
  congr 1
  have hh := congrArg (fun z ↦ edge s z) (hxy s)
  simpa only [← AddCommGrpCat.comp_apply, hres s] using hh

set_option linter.unusedVariables false in
-- STATEMENT-DISPUTED: the former codimension convention allowed infinite ambient
-- stalk dimensions. The returned E2 repair adds hfinite before using that convention.
/-- Descent in the bottom supported degree of a smooth pair with finite ambient stalk
Krull dimensions along the support. This finiteness makes the dimension equation a
finite codimension assertion.
Source: Stacks Tag 09XP, section-cohomology-support, Tags 09XQ, 015N and 0FUE;
main-20261015, sec-smooth-purity/sk-prop-an/lem-pur-frame-independence.proof.md.
(blueprint: lem-pur-relative-support-bottom-descent).

Proof:
1. Apply the separate relative smooth-pair vanishing theorem and transport along the
   canonical isomorphism from the support kernel to sectionsWithSupport.
2. The closed-support adjunction makes the support kernel preserve injectives.
   The kernel of two left-exact functors preserves finite limits. Evaluation is acyclic
   on its injective images. Use its
   canonical Grothendieck spectral object. Vanishing of rows below 2c makes the
   intervals (bottom,2c) zero in degrees 2c and 2c+1 by interval exactness. The same
   exact sequence makes the specified left edge invertible.
3. On a fixed injective resolution the edge cocycle description identifies the edge
   with the cycles-to-cohomology map. Evaluation restriction commutes with cycles
   and cohomology, hence with this edge. Conjugating by the kernel-normalized derived
   evaluation isomorphisms gives exactly the stated restriction square.
4. The already proved pro-etale comparison is invertible. Its conjugated restriction
   and transported edge therefore have the same invertibility and naturality.
5. At the terminal etale object the derived global-support comparison followed by
   derived evaluation is invertible. Compose it with the bottom edge. If two global
   classes restrict equally on a covering family, naturality says that their images
   are sections of the same cohomology sheaf agreeing on that cover. Sheaf separation
   and injectivity of this composite identify the classes. This includes empty covers
   and c=0. No orientation or chosen frame enters the descent argument. -/
theorem relative_support_bottom_descent
    (P : WeilConjectures.PurityFiniteSetting.{u}) (c d : ℕ)
    {B V Z U : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) (v : V ⟶ B)
    [SmoothOfRelativeDimension d v] (i : Z ⟶ V) [IsClosedImmersion i]
    [Smooth (i ≫ v)]
    (hcodim : ∀ z : Z,
      ringKrullDim (V.presheaf.stalk (i.base z)) =
        ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞))
    (hfinite : ∀ z : Z,
      ringKrullDim (V.presheaf.stalk (i.base z)) ≠ ⊤)
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
  let j := pullback.snd i e
  have hz : ∀ q : ℤ, q < 2 * (c : ℤ) →
      IsZero (relativeSupportCohomologySheaf P j r q) := by
    intro q hq
    have hz' := relative_support_vanishing P c d b v i hcodim hfinite e r q hq
    unfold relativeSupportCohomologySheaf
    let eK := Functor.rightDerivedFunctorPlusNatIso (relativeSupportKernelIso j)
    exact hz'.of_iso ((DerivedCategory.Plus.homologyFunctor
      (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) q).mapIso
        (eK.app ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (relativeSupportCoefficient P U r))))
  have he (W : U.Etale) : IsIso (relativeSupportEdge P j r (2 * c) W) :=
    relativeSupportEdge_isIso_of_vanishing P j r (2 * c)
      (fun q hq ↦ hz q (by exact_mod_cast hq)) W
  refine ⟨hz, he, ?_, ?_, ?_, ?_⟩
  · intro W W' a
    exact relativeSupportEdge_naturality P j r (2 * c) a
  · intro W
    have := he W
    exact ⟨inferInstance, by unfold relativeSupportProEdge; infer_instance⟩
  · intro W W' a
    dsimp only [relativeSupportProRestriction, relativeSupportProEdge]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [relativeSupportEdge_naturality P j r (2 * c) a]
  · intro ι W a hcover x y hxy
    let W₀ := Scheme.Etale.mk (𝟙 U)
    let X := relativeSupportCoefficient P U r
    let g : supportCohomology j (2 * c) X ⟶
        supportCohomology (pullback.snd j W₀.hom) (2 * c)
          ((relativeSupportRestriction W₀).obj X) :=
      (NatTrans.rightDerived (relativeSupportGlobalIso j).hom (2 * c)).app X ≫
      (relativeSupportDerivedEvaluation j W₀ (2 * c)).app X
    have hgd : IsIso (NatTrans.rightDerived (relativeSupportGlobalIso j).hom (2 * c)) :=
      relativeSupportGlobalDerived_isIso j (2 * c)
    have hdd : IsIso (relativeSupportDerivedEvaluation j W₀ (2 * c)) :=
      relativeSupportDerivedEvaluation_isIso j W₀ (2 * c)
    have hg : IsIso g := by dsimp only [g]; infer_instance
    have := he W₀
    let m : supportCohomology j (2 * c) X ⟶
        (relativeSupportCohomologySheaf P j r (2 * c)).obj.obj (op W₀) :=
      g ≫ relativeSupportEdge P j r (2 * c) W₀
    have hm : IsIso m := by dsimp only [m]; infer_instance
    apply relativeSupportSeparatedCover U.smallEtaleTopology
      (relativeSupportCohomologySheaf P j r (2 * c)) W₀ _ m W a hcover
      (fun s ↦ supportCohomology (pullback.snd j (W s).hom) (2 * c)
        ((relativeSupportRestriction (W s)).obj X))
      (fun s ↦ relativeSupportGlobalRestriction P j r (2 * c) (a s))
      (fun s ↦ relativeSupportEdge P j r (2 * c) (W s)) ?_ x y hxy
    intro s
    dsimp only [m]
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k ↦ g ≫ k)
      (relativeSupportEdge_naturality P j r (2 * c) (a s)).symm).trans ?_
    dsimp only [g, relativeSupportClassRestriction, relativeSupportGlobalRestriction]
    simp only [Category.assoc]
    change _ ≫ (asIso (relativeSupportDerivedEvaluation j W₀ (2 * c))).hom.app X ≫
      (asIso (relativeSupportDerivedEvaluation j W₀ (2 * c))).inv.app X ≫ _ = _
    rw [Iso.hom_inv_id_app_assoc]

end AlgebraicGeometry.Etale
