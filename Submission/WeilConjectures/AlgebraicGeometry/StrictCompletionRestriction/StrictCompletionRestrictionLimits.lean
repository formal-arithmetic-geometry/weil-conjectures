/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictCompletionRestrictionData
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.Limits
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
import all Submission.WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all Submission.WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
import all Mathlib.CategoryTheory.Limits.Preserves.Finite
import all Submission.WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability
import all Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Submission.WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer
import all Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.CategoryTheory.Sites.RegularEpi
import all Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import all Submission.WeilConjectures.CategoryTheory.InverseMateEquivalence
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import all Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import all Submission.WeilConjectures.Mathlib.CategoryTheory.NatIso
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Ring.FilteredColimits
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import all Submission.WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import all Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAction
import all Submission.WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import all Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import all Submission.WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
/-! # StrictCompletionRestrictionLimits -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
universe u
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.ProEtale.StrictCompletionRestriction
private theorem weaklyEtale_limits {X Y : Scheme.{u}} (f : X ⟶ Y) [hf : WeaklyEtale f] :
    PreservesLimitsOfSize.{u + 1, u + 1} (ProEtale.upperStar Ab.{u + 1} f) := by
  let := Scheme.ProEt.isContinuous_overMap hf
  let : PreservesLimitsOfSize.{u + 1, u + 1}
      (localizationRestriction Ab.{u + 1} f hf ⋙ sheafToPresheaf _ _) :=
    preservesLimits_of_natIso (Functor.sheafPushforwardContinuousCompSheafToPresheafIso
      _ _ _ _).symm
  let : PreservesLimitsOfSize.{u + 1, u + 1} (localizationRestriction Ab.{u + 1} f hf) :=
    preservesLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  exact preservesLimits_of_natIso (upperStarIsoLocalizationRestriction _ f hf).symm

private theorem module_limits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [PreservesLimitsOfSize.{u + 1, u + 1} (ProEtale.upperStar Ab.{u + 1} f)] :
    PreservesLimitsOfSize.{u + 1, u + 1} (CondensedRing.upperStar Λ f) := by
  let : MonObj (condensedRingObj Λ X) := (upperStarFromPoint X).monObjObj Λ
  let F := ProEtale.upperStar Ab.{u + 1} f
  let : F.Monoidal := inferInstanceAs (ProEtale.upperStar Ab.{u + 1} f).Monoidal
  let R := condensedRingObj Λ Y
  let : MonObj R := (upperStarFromPoint Y).monObjObj Λ
  let : MonObj (F.obj R) := F.monObjObj R
  let : PreservesLimitsOfSize.{u + 1, u + 1} (F.mapMod R ⋙ (Mod.forget (F.obj R) :
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (F.obj R) ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})) :=
    inferInstanceAs (PreservesLimitsOfSize.{u + 1, u + 1} (Mod.forget R ⋙ F))
  let : ReflectsLimitsOfSize.{u + 1, u + 1} ((Mod.forget (F.obj R) :
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (F.obj R) ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})) :=
    reflectsLimits_of_reflectsIsomorphisms
  let : PreservesLimitsOfSize.{u + 1, u + 1} (F.mapMod R) :=
    preservesLimits_of_reflects_of_preserves _
      ((Mod.forget (F.obj R) :
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (F.obj R) ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}))
  let : PreservesLimitsOfSize.{u + 1, u + 1}
      (Mod.extendScalars (condensedPullbackHom Λ f)) :=
    preservesLimits_of_natIso (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).symm
  exact inferInstanceAs (PreservesLimitsOfSize.{u + 1, u + 1}
    (F.mapMod R ⋙ Mod.extendScalars (condensedPullbackHom Λ f)))

/-- Inverse image along the multiplicative closure of immersions and weakly etale
maps preserves all limits in the coefficient universe.

Source: Stacks Tag 09AA and the localized-site description, Tags 00Y0 and 03DB
(blueprint: lem-sfb-strict-completion-restriction-limits).

Proof: For weakly etale maps identify inverse image with localized restriction.
Its composite with the sheaf inclusion preserves limits, and the inclusion reflects
them. For immersions use the immersion limit-preservation theorem. Limits of internal
modules are detected on underlying sheaves; extension along the coefficient isomorphism
is equivalent to restriction along its inverse, and preserves limits. The canonical
composition isomorphism proves the multiplicative-closure induction, including identity. -/
theorem strictCompletionRestrictionLimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : (MorphismProperty.multiplicativeClosure
      (fun {V W : Scheme.{u}} (g : V ⟶ W) ↦ IsImmersion g ∨ WeaklyEtale g)) f) :
    PreservesLimitsOfSize.{u + 1, u + 1} (CondensedRing.upperStar Λ f) := by
  have hbasic {V W : Scheme.{u}} (g : V ⟶ W) (hg : IsImmersion g ∨ WeaklyEtale g) :
      PreservesLimitsOfSize.{u + 1, u + 1} (CondensedRing.upperStar Λ g) := by
    rcases hg with hg | hg
    · let := hg
      let : PreservesLimitsOfSize.{u + 1, u + 1} (ProEtale.upperStar Ab.{u + 1} g) :=
        (Scheme.proEtale_immersion_inverseImage_preservesLimits g).2.1
      exact module_limits Λ g
    · let := hg
      let := weaklyEtale_limits g
      exact module_limits Λ g
  induction hf with
  | of f h => exact hbasic f h
  | id X =>
      let := weaklyEtale_limits (𝟙 X)
      exact module_limits Λ (𝟙 X)
  | comp_of f g hf hg ih =>
      let := ih
      let := hbasic g hg
      exact preservesLimits_of_natIso (CondensedRing.upperStarComp Λ f g).symm
end AlgebraicGeometry.ProEtale.StrictCompletionRestriction
