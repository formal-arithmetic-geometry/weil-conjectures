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
public import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
public import Sheaf.AlgebraicGeometry.SupportSiteComparison
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

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
import Sheaf.AlgebraicGeometry.SupportLongExact
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

All same-notion helpers below belong to the canonical interfaces of this node. Their
postponed proof obligations are named, documented and included in its declaration record.
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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- Exactness of etale restriction, for deriving the kernel-normalized comparison.
Source: Stacks Tag 03F3 (blueprint: lem-pur-relative-support-bottom-descent).
Proof: the localization functor is the inverse image, hence exact. -/
@[instance] theorem relativeSupportRestriction_colimits {U : Scheme.{u}} (W : U.Etale) :
    PreservesFiniteColimits (relativeSupportRestriction W) := by
  sorry

/-- Left exactness of etale restriction.
Source: Stacks Tag 03F3 (blueprint: lem-pur-relative-support-bottom-descent).
Proof: limits are computed sectionwise, so restriction preserves finite limits. -/
@[instance] theorem relativeSupportRestriction_limits {U : Scheme.{u}} (W : U.Etale) :
    PreservesFiniteLimits (relativeSupportRestriction W) := by
  sorry

/-- The derived restriction comparison attached to the kernel-normalized ordinary map.
Source: Stacks Tags 09XP and 015N
(blueprint: lem-pur-relative-support-bottom-descent). -/
noncomputable def relativeSupportDerivedEvaluation {Z U : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (W : U.Etale) (n : ℕ) :=
  Functor.rightDerivedBaseChange
    (β := relativeSupportRestriction W) (γ := 𝟭 AddCommGrpCat.{u + 1})
    ((Functor.rightUnitor _).hom ≫ (relativeSupportEvaluationIso i W).hom) n

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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

/-- Finite-coefficient support comparison is invertible for an arbitrary scheme.
Source: Stacks Tags 099V, 099W and 09XP
(blueprint: lem-pur-relative-support-bottom-descent).
Proof: the unit induces ordinary cohomology isomorphisms on T and its open complement
for finite torsion coefficients. The functorial support long exact sequences and the
five lemma identify supported cohomology in every degree; in degree zero use kernels.
No finite-type, separatedness or Noetherian assumption enters this argument. -/
@[instance] theorem relativeSupportProComparison_isIso (A : Type (u + 1)) [CommRing A]
    [Finite A] {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] (n : ℕ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    IsIso (relativeSupportProComparison A i n F) := by
  sorry

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
8. The site-comparison unit gives ordinary finite-coefficient cohomology comparison on
   W and its complement (thm-weil-pbc-site-comparison). Functoriality of the support long
   exact sequence (thm-pur-with-support-exactness) and the five lemma give the canonical
   supported comparison. Forgetting scalars computes the same support cohomology.
   Along the open complement, lem-weil-pbc-module-abelian-derived-direct-image-comparison
   makes scalar forgetting compatible with the derived direct image in localization.
   Its inverse transports the edge and restriction square to the pro-etale groups.
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
