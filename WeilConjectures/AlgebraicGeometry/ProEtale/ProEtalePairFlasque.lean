/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedSections
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

import WeilConjectures.AlgebraicGeometry.SupportCounterexample.ProEtaleInfiniteClopenPair
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
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
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
import WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Sites.RegularEpi
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.Mathlib.CategoryTheory.NatIso
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian

/-!
# Supported sections and flasqueness for a pro-etale open-closed pair

Source: blueprint sec-smooth-purity/sk-prop-a1-kummer/def-pur-flasque-support.md;
Stacks Project, Tags 03DA, 09BN and 09AH (blueprint: def-pur-flasque-support).

The existing `finiteSupportedSections` and `finiteClosedUpperShriek` give the kernel functor
and its closed inverse image. Constant-coefficient module sheaves are presented as
sheaves valued in `ModuleCat`, without a constructibility condition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The canonical comparison `G_Z ⟶ s_*s^!`, obtained by applying the closed
adjunction unit to the supported kernel. It is defined even when the open complement
is not quasi-compact. Source: blueprint def-pur-flasque-support, comparison paragraph;
Stacks Tag 09AH (blueprint: def-pur-flasque-support). -/
noncomputable def finiteSupportedClosedComparison (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X) :
    finiteSupportedSections Λ j ⟶
      finiteClosedUpperShriek Λ s j ⋙ lowerStar (ModuleCat.{u + 1} Λ) s :=
  Functor.whiskerLeft (finiteSupportedSections Λ j)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).unit

private local instance moduleSheaf_colimits (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) :
    HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) := by
  let : IsGrothendieckAbelian.{u + 1}
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology _ X
  exact IsGrothendieckAbelian.hasColimits _

/-- Both the supported-kernel functor and its closed inverse image are left exact.
Source: blueprint def-pur-flasque-support, left-exactness paragraph; Stacks Tag 03DA
(blueprint: def-pur-flasque-support).

Proof (step 3): a supported section in the kernel of a map lifts uniquely through
any preceding monomorphism, because kernels are sectionwise. Restricting the lift to
the open complement and using injectivity proves that this lift is itself supported.
The zero sheaf maps to zero, and induced kernel maps respect addition. This gives
left exactness of the supported-kernel functor. Apply the exact constant-coefficient
closed inverse image (`prop-weil-pbc-proetale-constant-exact`) to obtain left exactness
of its composite `finiteClosedUpperShriek`. No quasi-compactness is used. -/
theorem finiteSupportedSections_leftExact (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Z U : Scheme.{u}} (s : Z ⟶ X) [IsClosedImmersion s]
    (j : U ⟶ X) [IsOpenImmersion j]
    (hPair : IsCompl (Set.range s) (Set.range j)) :
    PreservesFiniteLimits (finiteSupportedSections Λ j) ∧
      PreservesFiniteLimits (finiteClosedUpperShriek Λ s j) := by
  have _ := hPair
  let C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)
  let D := parallelPair
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit 0
  have hD : PreservesFiniteLimits D.flip :=
    preservesFiniteLimits_of_evaluation _ (fun p ↦ by
      cases p
      · change PreservesFiniteLimits (𝟭 C)
        infer_instance
      · change PreservesFiniteLimits
          (upperStar (ModuleCat.{u + 1} Λ) j ⋙ lowerStar (ModuleCat.{u + 1} Λ) j)
        infer_instance)
  have hG : PreservesFiniteLimits (finiteSupportedSections Λ j) := by
    exact preservesFiniteLimits_of_natIso (limitIsoFlipCompLim D).symm
  exact ⟨hG, comp_preservesFiniteLimits _ _⟩

/-- With quasi-compact open complement, the specified natural comparison is an
isomorphism. Source: blueprint def-pur-flasque-support, comparison paragraph;
Stacks Tag 09AH (blueprint: def-pur-flasque-support).

Proof (step 2): step 1 identifies the restriction of the supported kernel to U with
zero, since there the restriction map is an identity. Apply the canonical-unit
clause of `lem-exc-proetale-closed-essential-image` to the supported kernel, with
its quasi-compact-complement hypothesis. This is precisely the displayed comparison,
and its naturality makes the objectwise isomorphisms a natural isomorphism. -/
theorem finiteSupportedClosedComparison_isIso (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] {X Z U : Scheme.{u}} (s : Z ⟶ X) [IsClosedImmersion s]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range s) (Set.range j)) :
    IsIso (finiteSupportedClosedComparison Λ s j) := by
  let C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)
  let L := upperStar (ModuleCat.{u + 1} Λ) j
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j
  have hz (M : C) : IsZero (L.obj ((finiteSupportedSections Λ j).obj M)) := by
    have hm : Mono (L.map (adj.unit.app M)) := by
      constructor
      intro Y a b hab
      have he := congrArg (fun f ↦ f ≫ adj.counit.app (L.obj M)) hab
      have ht : L.map (adj.unit.app M) ≫ adj.counit.app (L.obj M) = 𝟙 _ :=
        adj.left_triangle_components M
      simpa only [Category.assoc, ht, Category.comp_id] using he
    let e : (finiteSupportedSections Λ j).obj M ≅ kernel (adj.unit.app M) :=
      PreservesKernel.iso ((evaluation C C).obj M) adj.unit
    exact (isZero_kernel_of_mono (L.map (adj.unit.app M))).of_iso
      (L.mapIso e ≪≫ PreservesKernel.iso L (adj.unit.app M))
  have hi (M : C) : IsIso ((finiteSupportedClosedComparison Λ s j).app M) :=
    isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl s j hPair _ (hz M)
  exact NatIso.isIso_of_isIso_app _

private theorem immersion_upperStar_preservesLimits (Λ : Type (u + 1))
    [CommRing Λ] {X Z : Scheme.{u}} (s : Z ⟶ X) [IsImmersion s] :
    PreservesLimitsOfSize.{u + 1, u + 1} (upperStar (ModuleCat.{u + 1} Λ) s) := by
  let J := Scheme.ProEt.topology X
  let K := Scheme.ProEt.topology Z
  let F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ s
  let V := sheafCompose K (CategoryTheory.forget (ModuleCat.{u + 1} Λ))
  let U := CategoryTheory.forget (ModuleCat.{u + 1} Λ)
  have : U.PreservesLeftKanExtensions F.op := by
    intro P
    have : U.PreservesPointwiseLeftKanExtension P F.op := by
      intro c
      have : IsFiltered (CostructuredArrow F.op c) :=
        IsFiltered.of_equivalence (structuredArrowOpEquivalence F c.unop)
      have : PreservesFilteredColimitsOfSize.{u, u + 1} U :=
        preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} U
      exact Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit U P F.op c
    exact Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise U P F.op
  let e := sheafPullbackForgetIso J K F U
  have hv (T : Scheme.{u}) : PreservesLimitsOfSize.{u + 1, u + 1}
      (sheafCompose (Scheme.ProEt.topology T) U) := by
    have : PreservesLimitsOfSize.{u + 1, u + 1}
        (sheafCompose (Scheme.ProEt.topology T) U ⋙
          sheafToPresheaf (Scheme.ProEt.topology T) (Type (u + 1))) := by
      change PreservesLimitsOfSize.{u + 1, u + 1}
        (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ) ⋙
          (Functor.whiskeringRight T.ProEtᵒᵖ _ _).obj U)
      infer_instance
    exact preservesLimits_of_reflects_of_preserves _
      (sheafToPresheaf (Scheme.ProEt.topology T) (Type (u + 1)))
  let : PreservesLimitsOfSize.{u + 1, u + 1} V := hv Z
  let : PreservesLimitsOfSize.{u + 1, u + 1} (sheafCompose J U) := hv X
  let : PreservesLimitsOfSize.{u + 1, u + 1}
      (Scheme.proEtaleSheafInverseImage s (Type (u + 1))) :=
    (Scheme.proEtale_immersion_inverseImage_preservesLimits s).1
  let : ReflectsLimitsOfSize.{u + 1, u + 1} V := reflectsLimits_of_reflectsIsomorphisms
  let : PreservesLimitsOfSize.{u + 1, u + 1}
      (upperStar (ModuleCat.{u + 1} Λ) s ⋙ V) := preservesLimits_of_natIso e.symm
  exact preservesLimits_of_reflects_of_preserves _ V

/-- A colimit of module sheaves is the sheafification of the presheaf colimit.
The comparison is the sheafification unit followed by an isomorphism, so is locally
surjective on underlying sections. -/
private theorem colimit_comparison_locally_surjective
    (Λ : Type (u + 1)) [CommRing Λ]
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    [HasSheafify J (ModuleCat.{u + 1} Λ)]
    [J.WEqualsLocallyBijective (ModuleCat.{u + 1} Λ)]
    {K : Type (u + 1)} [SmallCategory K]
    (D : K ⥤ Sheaf J (ModuleCat.{u + 1} Λ)) (c : Limits.Cocone D) (hc : Limits.IsColimit c) :
    Presheaf.IsLocallySurjective J
      (Limits.colimit.desc (D ⋙ sheafToPresheaf J (ModuleCat.{u + 1} Λ))
        ((sheafToPresheaf J (ModuleCat.{u + 1} Λ)).mapCocone c)) := by
  let U := sheafToPresheaf J (ModuleCat.{u + 1} Λ)
  let L := presheafToSheaf J (ModuleCat.{u + 1} Λ)
  let adj : L ⊣ U := sheafificationAdjunction J (ModuleCat.{u + 1} Λ)
  let P := Limits.colimit.cocone (D ⋙ U)
  let hP := Limits.colimit.isColimit (D ⋙ U)
  let hQ := Limits.isColimitOfPreserves L hP
  let e : (D ⋙ U) ⋙ L ≅ D := Functor.isoWhiskerLeft D (asIso adj.counit)
  let hcE := (Limits.IsColimit.precomposeHomEquiv e c).symm hc
  let θ := hQ.coconePointUniqueUpToIso hcE
  let k := adj.unit.app P.pt ≫ U.map θ.hom
  have hk (i : K) : P.ι.app i ≫ k = U.map (c.ι.app i) := by
    dsimp only [k]
    have hn := adj.unit.naturality (P.ι.app i)
    change P.ι.app i ≫ adj.unit.app P.pt =
      adj.unit.app (U.obj (D.obj i)) ≫ U.map (L.map (P.ι.app i)) at hn
    rw [← Category.assoc, hn, Category.assoc, ← U.map_comp]
    have hθ := hQ.comp_coconePointUniqueUpToIso_hom hcE i
    change L.map (P.ι.app i) ≫ θ.hom = adj.counit.app (D.obj i) ≫ c.ι.app i at hθ
    rw [hθ, U.map_comp, ← Category.assoc, adj.right_triangle_components]
    exact Category.id_comp _
  have heq : Limits.colimit.desc (D ⋙ U) (U.mapCocone c) = k := by
    apply hP.hom_ext
    intro i
    exact (hP.fac _ i).trans (hk i).symm
  rw [heq]
  have : Presheaf.IsLocallySurjective J
      (adj.unit.app P.pt) := by
    change Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P.pt)
    infer_instance
  infer_instance

private noncomputable def continuousModulePresheaf (Λ : Type (u + 1))
    [CommRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ] :
    Scheme.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} Λ where
  obj V := ModuleCat.of Λ C(V.unop, Λ)
  map f := ModuleCat.ofHom
    { toFun := fun g ↦ g.comp f.unop.base.hom
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

private noncomputable def rankOne (Λ : Type (u + 1)) [CommRing Λ]
    (T : Scheme.{u}) : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ) := by
  let : TopologicalSpace Λ := ⊥
  let : DiscreteTopology Λ := ⟨rfl⟩
  let P := continuousModulePresheaf Λ
  have : PreservesLimitsOfSize.{u, u + 1}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have hP : Presheaf.IsSheaf Scheme.proetaleTopology P := by
    let : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} Λ) :=
      ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
    let : ReflectsLimitsOfSize.{u, u + 1}
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
      reflectsLimits_of_reflectsIsomorphisms
    apply Presheaf.isSheaf_of_isSheaf_comp Scheme.proetaleTopology P
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    exact .of_le Scheme.proetaleTopology_le_fpqcTopology
      (isSheaf_fpqcTopology_continuousMapPresheafAb Λ)
  exact ((Scheme.ProEt.forget T ⋙ Over.forget T).sheafPushforwardContinuous _ _
    Scheme.proetaleTopology).obj ⟨P, hP⟩

private theorem map_sumToProduct_epi
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    {I : Type*} [DecidableEq I] (H : I → C) [HasProduct H] [HasCoproduct H]
    (E : C ⥤ D) [E.PreservesZeroMorphisms]
    [PreservesLimit (Discrete.functor H) E] (n : I)
    (hz : ∀ i, i ≠ n → IsZero (E.obj (H i))) :
    Epi (E.map (Sigma.desc (fun i ↦ Pi.ι H i))) := by
  let c := Sigma.desc (fun i ↦ Pi.ι H i)
  have hr : E.map (Pi.π H n) ≫ E.map (Sigma.ι H n) ≫ E.map c = 𝟙 _ := by
    apply (isLimitOfPreserves E (productIsProduct H)).hom_ext
    rintro ⟨i⟩
    change (E.map (Pi.π H n) ≫ E.map (Sigma.ι H n) ≫ E.map c) ≫
      E.map (Pi.π H i) = (𝟙 _) ≫ E.map (Pi.π H i)
    by_cases hi : i = n
    · subst i
      simp only [Category.assoc, ← E.map_comp, c, Sigma.ι_desc_assoc,
        Pi.ι_π_eq_id, Category.comp_id, Category.id_comp]
    · exact (hz i hi).eq_of_tgt _ _
  exact epi_of_epi_fac (f := E.map (Pi.π H n) ≫ E.map (Sigma.ι H n))
    (h := 𝟙 _) (by simpa only [Category.assoc] using hr)

private theorem sumToProduct_not_epi
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) [IsAffine X]
    (I : Type (u + 1)) [Infinite I] [DecidableEq I]
    (H : I → Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (z : ∀ i, (H i).obj.obj (op (Scheme.ProEt.mk (𝟙 X))))
    (hz : ∀ i, z i ≠ 0) :
    ¬ Epi (Sigma.desc (fun i ↦ Pi.ι H i)) := by
  classical
  let W := Scheme.ProEt.mk (𝟙 X)
  let : IsAffine W.left := inferInstanceAs (IsAffine X)
  let ev := sheafToPresheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) ⋙
    (evaluation X.ProEtᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op W)
  let e := PreservesProduct.iso ev H ≪≫
    ModuleCat.piIsoPi.{u + 1, u + 1, u + 1} (fun i ↦ ev.obj (H i))
  let t := e.inv z
  have ht (i : I) : (Pi.π H i).hom.app (op W) t = z i := by
    have he : e.inv ≫ ev.map (Pi.π H i) =
        ModuleCat.ofHom (LinearMap.proj i) := by
      dsimp only [e, Iso.trans_inv]
      have hi : (PreservesProduct.iso ev H).inv = inv (piComparison ev H) := by
        apply (cancel_mono (piComparison ev H)).mp
        simp only [← PreservesProduct.iso_hom, Iso.inv_hom_id, IsIso.inv_hom_id]
      rw [Category.assoc, hi, inv_piComparison_comp_map_π]
      exact ModuleCat.piIsoPi_inv_kernel_ι _ i
    exact congrArg (fun f ↦ f z) he
  let c := Sigma.desc (fun i ↦ Pi.ι H i)
  intro hc
  have : Sheaf.IsLocallySurjective c :=
    (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{u + 1} Λ) c).mpr hc
  let D := CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor H)
  let cs := CoproductsFromFiniteFiltered.finiteSubcoproductsCocone H
  let hcs := CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone H
  let U := sheafToPresheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)
  let F := D ⋙ U
  let k := colimit.desc F (U.mapCocone cs)
  let q := k ≫ c.hom
  have : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) k :=
    colimit_comparison_locally_surjective Λ D cs hcs
  have : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) q := by
    dsimp [q]
    infer_instance
  obtain ⟨A, hA, V, f, hcover, hf⟩ := Scheme.ProEt.finite_cover_refinement X W
    (Presheaf.imageSieve q t) (Presheaf.imageSieve_mem (Scheme.ProEt.topology X) q t)
  let := hA
  have hrep (a : A) : ∃ (S : Finset (Discrete I))
      (y : (∐ (fun i : S ↦ H i.val.as)).obj.obj (op (V a))),
      (Sigma.desc (f := fun i : S ↦ H i.val.as) (fun i ↦ Pi.ι H i.val.as)).hom.app
        (op (V a)) y = (∏ᶜ H).obj.map (f a).op t := by
    obtain ⟨y, hy⟩ := hf a
    let E := (evaluation X.ProEtᵒᵖ (ModuleCat.{u + 1} Λ)).obj
      (op (V a)) ⋙ CategoryTheory.forget _
    have : PreservesColimit F E := by dsimp [E]; infer_instance
    obtain ⟨S, y', hy'⟩ := Types.jointly_surjective (F ⋙ E)
      (isColimitOfPreserves E (colimit.isColimit F)) y
    refine ⟨S, y', ?_⟩
    have hk := colimit.ι_desc (U.mapCocone cs) S
    have hk' := congrArg (fun g ↦ g.app (op (V a)) y') hk
    change k.app (op (V a)) ((colimit.ι F S).app (op (V a)) y') =
      (cs.ι.app S).hom.app (op (V a)) y' at hk'
    change (colimit.ι F S).app (op (V a)) y' = y at hy'
    rw [hy'] at hk'
    have he : cs.ι.app S ≫ c =
        Sigma.desc (f := fun i : S ↦ H i.val.as) (fun i ↦ Pi.ι H i.val.as) := by
      apply Sigma.hom_ext
      intro i
      simp [cs, c, CoproductsFromFiniteFiltered.finiteSubcoproductsCocone]
    rw [← he]
    change c.hom.app (op (V a)) ((cs.ι.app S).hom.app (op (V a)) y') = _
    rw [← hk']
    exact hy
  let : Fintype A := Fintype.ofFinite A
  choose S y hy using hrep
  let B : Finset I := (Finset.univ.biUnion S).image Discrete.as
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset B
  have hzero (a : A) : (H n).obj.map (f a).op (z n) = 0 := by
    rw [← ht n, ← NatTrans.naturality_apply (Pi.π H n).hom, ← hy a]
    have he : Sigma.desc (f := fun i : S a ↦ H i.val.as)
        (fun i ↦ Pi.ι H i.val.as) ≫ Pi.π H n = 0 := by
      apply Sigma.hom_ext
      intro i
      have hne : i.val.as ≠ n := by
        intro hi
        apply hn
        exact Finset.mem_image.mpr ⟨i.val,
          Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, i.property⟩, hi⟩
      simp [Pi.ι_π_of_ne H hne]
    exact congrArg (fun g ↦ g.hom.app (op (V a)) (y a)) he
  apply hz n
  let G := (sheafCompose (Scheme.ProEt.topology X)
    (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj (H n)
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp G.property).isSheafFor _ hcover).isSeparatedFor.ext
  intro Y g hg
  obtain ⟨a⟩ := hg
  change (H n).obj.map (f a).op (z n) = (H n).obj.map (f a).op 0
  exact (hzero a).trans (map_zero _).symm

private theorem supportedComparison_not_isIso_of_vanish
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hM : ¬ IsZero M)
    (hj : IsZero ((upperStar (ModuleCat.{u + 1} Λ) j).obj M))
    (hs : IsZero ((upperStar (ModuleCat.{u + 1} Λ) s).obj M)) :
    ¬ IsIso ((finiteSupportedClosedComparison Λ s j).app M) := by
  let C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j
  let η := adj.unit.app M
  let e : (finiteSupportedSections Λ j).obj M ≅ kernel η :=
    PreservesKernel.iso ((evaluation C C).obj M) adj.unit
  have hη : η = 0 := ((lowerStar (ModuleCat.{u + 1} Λ) j).map_isZero hj).eq_zero_of_tgt η
  have : IsIso (kernel.ι η) := by rw [hη]; infer_instance
  let e' : (finiteSupportedSections Λ j).obj M ≅ M :=
    e ≪≫ (asIso (kernel.ι η))
  have hz : IsZero ((finiteClosedUpperShriek Λ s j).obj M) :=
    hs.of_iso ((upperStar (ModuleCat.{u + 1} Λ) s).mapIso e')
  intro h
  have hh := ((lowerStar (ModuleCat.{u + 1} Λ) s).map_isZero hz).of_iso
    (asIso ((finiteSupportedClosedComparison Λ s j).app M))
  exact hM (hh.of_iso e'.symm)

private theorem clopen_family_counterexample
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [Nontrivial Λ]
    (X : Scheme.{u}) [IsAffine X] (I : Type (u + 1)) [Infinite I]
    (W : I → X.Opens) [∀ i, IsClosedImmersion (W i).ι]
    (hW : ∀ i, Nonempty (W i))
    (hdisj : Pairwise (fun i j ↦ Disjoint (W i) (W j)))
    {Z : Scheme.{u}} (s : Z ⟶ X) [IsClosedImmersion s]
    (hpair : IsCompl (Set.range s) (Set.range (⨆ i, W i).ι)) :
    ∃ M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ),
      ¬ IsIso ((finiteSupportedClosedComparison Λ s (⨆ i, W i).ι).app M) := by
  classical
  let : TopologicalSpace Λ := ⊥
  let : DiscreteTopology Λ := ⟨rfl⟩
  let A := ModuleCat.{u + 1} Λ
  let H := fun i ↦ (lowerStar A (W i).ι).obj (rankOne Λ (W i))
  let c := Sigma.desc (fun i ↦ Pi.ι H i)
  let M := cokernel c
  have hn : ¬ Epi c := by
    let z : ∀ i, (H i).obj.obj (op (Scheme.ProEt.mk (𝟙 X))) :=
      fun i ↦ ContinuousMap.const _ 1
    apply sumToProduct_not_epi Λ X I H z
    intro i h
    have hp : Nonempty ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (W i).ι).obj
        (Scheme.ProEt.mk (𝟙 X))).left := by
      obtain ⟨x⟩ := hW i
      obtain ⟨y, -, -⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := 𝟙 X) (g := (W i).ι) ((W i).ι x) x (by simp)
      exact ⟨y⟩
    obtain ⟨x⟩ := hp
    exact one_ne_zero (congrArg (fun f : C(
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (W i).ι).obj
        (Scheme.ProEt.mk (𝟙 X))).left, Λ) ↦ f x) h)
  have hM : ¬ IsZero M := by
    intro hz
    exact hn (Preadditive.epi_of_isZero_cokernel c hz)
  have hsH (i : I) : IsZero ((upperStar A s).obj (H i)) := by
    have hd : Set.range (W i).ι.base ∩ Set.range s.base = ∅ := by
      rw [Scheme.Opens.range_ι]
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hx' : x ∈ Set.range (⨆ i, W i).ι := by
        rw [Scheme.Opens.range_ι]
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx.1⟩
      exact Set.disjoint_left.mp hpair.disjoint hx.2 hx'
    have he : IsIso (openImmersionLowerShriekToLowerStar A (W i).ι) :=
      isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A (W i).ι
        (IsClosedImmersion.isClosedEmbedding (W i).ι).isClosed_range
    exact (isZero_upperStar_openImmersionLowerShriek A (W i).ι s hd _).of_iso
      ((upperStar A s).mapIso
        (asIso ((openImmersionLowerShriekToLowerStar A (W i).ι).app (rankOne Λ (W i)))).symm)
  have hsP : IsZero ((upperStar A s).obj (∏ᶜ H)) := by
    let : PreservesLimitsOfSize.{u + 1, u + 1} (upperStar A s) :=
      immersion_upperStar_preservesLimits Λ s
    exact (isLimitOfPreserves (upperStar A s) (productIsProduct H)).isZero_pt
      (Functor.isZero _ (fun i ↦ hsH i.as))
  have hsM : IsZero ((upperStar A s).obj M) :=
    hsP.of_epi ((upperStar A s).map (cokernel.π c))
  have hlocal (n : I) : IsZero ((openImmersionRestriction A (W n).ι).obj M) := by
    let E := openImmersionRestriction A (W n).ι
    let : E.IsLeftAdjoint := (openImmersionRestrictionLowerStarAdjunction A (W n).ι).isLeftAdjoint
    have hz (i : I) (hi : i ≠ n) : IsZero (E.obj (H i)) := by
      apply isZero_openImmersionRestriction_lowerStar A (W i).ι (W n).ι
      · simpa only [Scheme.Opens.range_ι] using
          (Set.disjoint_iff_inter_eq_empty.mp
            (TopologicalSpace.Opens.coe_disjoint.mpr (hdisj hi)))
    have : Epi (E.map c) := map_sumToProduct_epi H E n hz
    exact (isZero_cokernel_of_epi (E.map c)).of_iso (PreservesCokernel.iso E c)
  have hjM : IsZero ((upperStar A (⨆ i, W i).ι).obj M) := by
    let O : X.Opens := ⨆ i, W i
    let g (i : I) := X.homOfLE (show W i ≤ O from le_iSup W i)
    have : ∀ i, IsOpenImmersion (g i) := fun i ↦ inferInstance
    have hcover : Presieve.ofArrows (fun i ↦ (W i : Scheme.{u})) g ∈
        Scheme.proetalePrecoverage O := by
      apply Scheme.zariskiPrecoverage_le_proetalePrecoverage
      apply (Scheme.ofArrows_mem_precoverage_iff _).mpr
      refine ⟨?_, fun i ↦ inferInstance⟩
      intro x
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp x.property
      exact ⟨i, ⟨⟨x.val, hi⟩, by
        apply Subtype.ext
        exact congrArg (fun f : (W i : Scheme.{u}) ⟶ X ↦ f ⟨x.val, hi⟩)
          (X.homOfLE_ι (show W i ≤ O from le_iSup W i))⟩⟩
    have hz : IsZero ((openImmersionRestriction A O.ι).obj M) := by
      have : IsIso (0 : (openImmersionRestriction A O.ι).obj M ⟶
          (openImmersionRestriction A O.ι).obj M) := by
        apply isIso_of_isIso_localizationRestriction A _ g hcover
        intro i
        have hz' : IsZero ((localizationRestriction A (g i) inferInstance).obj
            ((openImmersionRestriction A O.ι).obj M)) := by
          let ei := (upperStarIsoLocalizationRestriction A (g i) inferInstance).app
            ((openImmersionRestriction A O.ι).obj M)
          let eo := (upperStar A (g i)).mapIso
            ((upperStarIsoOpenImmersionRestriction A O.ι).app M)
          let ec := (upperStarComp A (g i) O.ι).app M
          have hi : g i ≫ O.ι = (W i).ι := X.homOfLE_ι _
          have hz'' : IsZero ((upperStar A (g i ≫ O.ι)).obj M) := by
            rw [hi]
            exact (hlocal i).of_iso
              ((upperStarIsoOpenImmersionRestriction A (W i).ι).app M)
          exact hz''.of_iso (ei.symm ≪≫ eo.symm ≪≫ ec.symm)
        exact hz'.isIso hz' _
      exact IsZero.of_mono_zero _ ((openImmersionRestriction A O.ι).obj M)
    exact hz.of_iso ((upperStarIsoOpenImmersionRestriction A O.ι).app M)
  exact ⟨M, supportedComparison_not_isIso_of_vanish Λ s _ M hM hjM hsM⟩

/-- The comparison can fail for an affine base and a non-quasi-compact complement,
with any nonzero finite commutative coefficient ring. Source: the counterexample in
steps 5--7 of node def-pur-flasque-support (blueprint: def-pur-flasque-support).

Proof:
5. Take a field k, R = product over positive integers of k, and the ideal J of
finite-support sequences. Set X = Spec R, Z = Spec (R/J), and let U be the union of
the pairwise disjoint clopen coordinate points X_n. This open is not quasi-compact.
Let H_n be the direct image of the constant rank-one sheaf from X_n. In P = product
of H_n let S be tuples locally of finite coordinate support. The sheaf condition
and finite-support gluing identify S with the coproduct. Put F = coker(S ⟶ P).
6. The closed inverse image kills each H_n: every indexing object can be restricted
to the complement of X_n. Closed inverse image preserves products by
`lem-weil-pbc-proetale-immersion-limit-preservation` and preserves coproducts by its
adjunction, so it kills P and S. Its exactness kills F. Open restriction of S ⟶ P
is an isomorphism on each X_n, so j^*F = 0 as well.
7. On an affine object, the finite affine refinement of a pro-etale cover shows
that a section of S has globally finite coordinate support. The tuple (1,1,...)
over X therefore is not in S(X). Sectionwise kernels imply its image in F(X) is
nonzero. Hence G_Z F = F is nonzero whereas s^!F = 0, and the comparison is not
an isomorphism. The module-sheaf product/coproduct facts are
`lem-weil-pbc-module-sheaves-colimits-forgetful`, and inverse-image exactness is
`prop-weil-pbc-proetale-constant-exact`. -/
theorem exists_finiteSupportedClosedComparison_not_isIso (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [Nontrivial Λ] :
    ∃ (X Z U : Scheme.{u}) (s : Z ⟶ X) (j : U ⟶ X),
      IsAffine X ∧ IsClosedImmersion s ∧ IsOpenImmersion j ∧
      IsCompl (Set.range s) (Set.range j) ∧ ¬ QuasiCompact j ∧
      ∃ M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ),
        ¬ IsIso ((finiteSupportedClosedComparison Λ s j).app M) := by
  classical
  let k := ULift.{u} (ZMod 2)
  let I := ULift.{u} ℕ
  let X := SupportCounterexample.base k I
  let s := SupportCounterexample.closedInclusion k I
  let O := SupportCounterexample.openPart k I
  obtain ⟨hs, hp, hqc, hw, hd⟩ := SupportCounterexample.pair_properties k I
  let : IsClosedImmersion s := hs
  let : ∀ i, IsClosedImmersion (SupportCounterexample.piece k I i).ι := fun i ↦ (hw i).1
  have hO : (⨆ i : ULift.{u + 1} I,
      SupportCounterexample.piece k I i.down) = O := by
    apply le_antisymm
    · exact iSup_le (fun i ↦ le_iSup (SupportCounterexample.piece k I) i.down)
    · exact iSup_le (fun i ↦ le_iSup_of_le (ULift.up i) le_rfl)
  obtain ⟨M, hM⟩ := clopen_family_counterexample Λ X (ULift.{u + 1} I)
    (fun i ↦ SupportCounterexample.piece k I i.down)
    (fun i ↦ (hw i.down).2) (by
      intro i j hij
      exact hd (fun h ↦ hij (ULift.ext _ _ h))) s (by rw [hO]; exact hp)
  exact ⟨X, SupportCounterexample.closed k I, O, s, O.ι,
    inferInstance, hs, inferInstance, hp, hqc, M, by rw [hO] at hM; exact hM⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
end AlgebraicGeometry.ProEtale
