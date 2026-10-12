/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.FullAffineEtaleSite
public import Sheaf.CategoryTheory.SpecialCocontinuousCoverings
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.AlgebraicGeometry.KInjectiveResolutions
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Affine étale restriction and cohomology

Source: Stacks Project, Topologies 04HR, Definitions 0219 and 021B(4), and
Cohomology on Sites 03YU (blueprint: lem-weil-pbc-affine-etale-site-topos).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks 04HR (blueprint: lem-weil-pbc-affine-etale-site-topos).
Proof: standard coverings are étale coverings and affine pullbacks are computed in the
small étale site, so the sheaf equalizer condition restricts to the affine site. -/
theorem fullAffineEtaleInclusion_isContinuous (S : Scheme.{u}) :
    (fullAffineEtaleInclusion S).IsContinuous
      (fullAffineEtaleTopology S) S.smallEtaleTopology := by sorry

attribute [instance] fullAffineEtaleInclusion_isContinuous

/-- Source: Stacks 04HR (blueprint: lem-weil-pbc-affine-etale-site-topos).
Proof:
1. Affine pullbacks and finite jointly surjective étale families give the site axioms
   (lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-etale-covering-base-change).
2. Any étale cover of an affine object admits a finite affine refinement
   (lem-weil-pbc-etale-covering-affine-refinement), proving cocontinuity. Standard covers
   remain covers and pullbacks are preserved, proving continuity. Full faithfulness gives
   local equality and lifting using identity covers. Affine open covers give image covers.
3. These refinements identify the standard topology with the induced topology.
4. Compare the full affine subcategory with the category of spectra via the fully faithful,
   essentially surjective spectrum functor. Its induced sheaf equivalence
   (lem-weil-pbc-affine-etale-induced-sheaf-equivalence), transported by
   lem-weil-pbc-site-equivalence-sheaf-transport, gives the restriction equivalence for both
   sets and abelian groups. -/
theorem fullAffineEtaleInclusion_special_equivalences (S : Scheme.{u}) :
    (fullAffineEtaleInclusion S).IsSpecialCocontinuousForCoverings
      (fullAffineEtalePrecoverage S) S.smallEtalePretopology.toPrecoverage ∧
    ((fullAffineEtaleInclusion S).sheafPushforwardContinuous (Type u)
      (fullAffineEtaleTopology S) S.smallEtaleTopology).IsEquivalence ∧
    ((fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
      (fullAffineEtaleTopology S) S.smallEtaleTopology).IsEquivalence := by sorry

/-- Source: Stacks 03YU, applied to the equivalence of 04HR
(blueprint: lem-weil-pbc-affine-etale-site-topos).
Proof (step 5 of the node): restriction is an additive equivalence, so preserves injectives
and injective resolutions (lem-weil-pbc-equivalence-injective-resolutions). Evaluation at U
of the restricted resolution is exactly evaluation at its image of the original resolution,
with identical differentials. Taking cohomology gives the comparison. Lifts of sheaf maps
and homotopies restrict, so this is natural in the sheaf and independent of resolutions.
In degree zero the augmentations are identical, giving the identity on sections
(lem-weil-pbc-left-exact-injective-resolution-degree-zero). The two explicit evaluations
below are the canonical Ext-zero/sheafification/yoneda identifications with sections. -/
theorem fullAffineEtale_cohomology_comparison (S : Scheme.{u})
    [HasExt.{w} (Sheaf (fullAffineEtaleTopology S) AddCommGrpCat.{u})]
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    (U : S.FullAffineEtale) :
    ∃ e : ∀ p : ℕ,
      (fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
          (fullAffineEtaleTopology S) S.smallEtaleTopology ⋙
        Sheaf.cohomologyPresheafFunctor.{w} (fullAffineEtaleTopology S) p ⋙
          (CategoryTheory.evaluation _ _).obj (op U) ≅
      Sheaf.cohomologyPresheafFunctor.{w} S.smallEtaleTopology p ⋙
        (CategoryTheory.evaluation _ _).obj (op U.obj),
    ∀ (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
      (x : Sheaf.H'.{w}
        (((fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
          (fullAffineEtaleTopology S) S.smallEtaleTopology).obj G) 0 U),
      (((sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u}).homEquiv _ _
        (Ext.homEquiv₀ (((e 0).app G).hom x))).app (op U.obj))
          (FreeAbelianGroup.of (𝟙 U.obj)) =
      (((sheafificationAdjunction (fullAffineEtaleTopology S) AddCommGrpCat.{u}).homEquiv
        _ _ (Ext.homEquiv₀ x)).app (op U)) (FreeAbelianGroup.of (𝟙 U)) := by sorry

/-- Source: Stacks 03YU and 04HR (blueprint: lem-weil-pbc-affine-etale-site-topos).
Proof (step 6): the identity of S is terminal in the small étale site. Thus cohomology over
this object is global étale cohomology. An injective resolution is bounded below and hence
K-injective, so computes the same global derived cohomology; independence follows from
homotopy equivalence of resolutions (prop-weil-pbc-kinjective-resolutions-exist).
When S is affine, apply the preceding objectwise comparison to this identity object.
The global cohomology is written as the established Ext encoding `Sheaf.functorH`, whose
comparison with `Etale.cohomology` is the project's stage-3 bridge. -/
theorem fullAffineEtale_cohomology_base (S : Scheme.{u}) [IsAffine S]
    [HasExt.{w} (Sheaf (fullAffineEtaleTopology S) AddCommGrpCat.{u})]
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})] (p : ℕ) :
    Nonempty
      (Sheaf.cohomologyPresheafFunctor.{w} S.smallEtaleTopology p ⋙
        (CategoryTheory.evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 S))) ≅
        Sheaf.functorH.{w, u} S.smallEtaleTopology p) ∧
    Nonempty
      ((fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
        (fullAffineEtaleTopology S) S.smallEtaleTopology ⋙
        Sheaf.cohomologyPresheafFunctor.{w} (fullAffineEtaleTopology S) p ⋙
          (CategoryTheory.evaluation _ _).obj (op (⟨Scheme.Etale.mk (𝟙 S), ‹IsAffine S›⟩ :
            S.FullAffineEtale)) ≅ Sheaf.functorH.{w, u} S.smallEtaleTopology p) := by sorry

end AlgebraicGeometry.Scheme
