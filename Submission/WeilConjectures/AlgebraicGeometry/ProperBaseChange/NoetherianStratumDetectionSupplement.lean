/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import Submission.WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Submission.WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Mathlib.Algebra.Category.Grp.AB
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import all Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Submission.WeilConjectures.AlgebraicGeometry.NoetherianStratumDetection

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Detection by pro-etale covers of finitely many locally closed strata

Source: Stacks Project, Tags 09AH and 09AB, followed by finite-stratum induction
(blueprint: lem-weil-pbc-noetherian-stratum-detection).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Abelian sheaves are detected by the chosen pro-etale covers of all strata.
Source: Stacks, Tags 09AH and 09AB, and finite-stratum induction
(blueprint: lem-weil-pbc-noetherian-stratum-detection).
Proof: adjunction and the sectionwise base-change formula for direct image identify
successive inverse images with inverse image along the composite, including identities.
For a covering, localization identifies inverse image with slice restriction; the sheaf
separatedness axiom on base-changed covers detects zero sections. Thus covering
restrictions detect zero sheaves. Induct on the number of nonempty strata. The empty
scheme has only zero abelian sheaves by the empty-cover axiom. Factor each stratum as a
closed immersion into an open neighborhood. Those neighborhoods cover X. Their open
complements are Noetherian and their open inclusions are quasi-compact. Base change the
remaining strata to the complement and discard the empty chosen stratum; induction
makes the restriction there zero. The closed restriction is also zero. The exact
open/closed sequence of Tag 09AH gives zero on each neighborhood; covering detection
gives zero globally. Actual immersion structures are retained, also for nonreduced strata.
The constant integer sheaf action allows use of module localization and detection. -/
theorem proEtale_isZero_of_stratum_cover (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X] (S : Stratification X)
    (V : ∀ a : Fin S.n, Scheme.Cover.{w} proetalePrecoverage (S.domain a))
    (F : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1})
    (hF : ∀ (a : Fin S.n) (j : (V a).I₀),
      IsZero ((proEtaleSheafInverseImage ((V a).f j ≫ S.immersion a)
        AddCommGrpCat.{u + 1}).obj F)) : IsZero F := by
  -- Finite quasi-compact joint detection applies directly to the actual immersions.
  have : IsNoetherian X := {}
  have hstr (a : Fin S.n) :
      IsZero ((proEtaleSheafInverseImage (S.immersion a) AddCommGrpCat.{u + 1}).obj F) := by
    let G := (proEtaleSheafInverseImage (S.immersion a) AddCommGrpCat.{u + 1}).obj F
    let := HasZeroObject.zero'
      (Sheaf (ProEt.topology (S.domain a)) AddCommGrpCat.{u + 1})
    let : ∀ j, WeaklyEtale ((V a).f j) :=
      (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1 (V a).mem₀.2 |>.2
    have hz (j : (V a).I₀) :
        IsZero ((AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1}
          ((V a).f j)).obj G) :=
      (hF a j).of_iso ((AlgebraicGeometry.ProEtale.upperStarComp
        AddCommGrpCat.{u + 1} ((V a).f j) (S.immersion a)).symm.app F)
    have : IsIso (0 : G ⟶ 0) := by
      refine AlgebraicGeometry.ProEtale.isIso_of_isIso_localizationRestriction
        AddCommGrpCat.{u + 1} (0 : G ⟶ 0) (V a).f (V a).mem₀ fun j ↦ ?_
      let e := AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction
        AddCommGrpCat.{u + 1} ((V a).f j) inferInstance
      exact isIso_of_source_target_iso_zero _ ((hz j).of_iso (e.app G).symm).isoZero
        (((AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1}
          ((V a).f j)).map_isZero (isZero_zero _)).of_iso (e.app 0).symm).isoZero
    exact (isZero_zero _).of_iso (asIso (0 : G ⟶ 0))
  have : ∀ a : Fin S.n, TopologicalSpace.NoetherianSpace (S.domain a) := fun a ↦
    (S.immersion a).isEmbedding.noetherianSpace
  have : ∀ a : Fin S.n, QuasiCompact (S.immersion a) := fun a ↦ inferInstance
  rw [IsZero.iff_id_eq_zero]
  apply AlgebraicGeometry.ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp S.immersion
  · intro x
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
    exact ⟨a, (S.range_immersion a).symm ▸ ha⟩
  · intro a
    rw [(AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1}
      (S.immersion a)).map_id]
    exact (hstr a).eq_of_src _ _

end AlgebraicGeometry.Scheme
