/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Affine étale restriction and cohomology

Source: Stacks Project, Topologies 04HR, Definitions 0219 and 021B(4), and
Cohomology on Sites 03YU (blueprint: lem-weil-pbc-affine-etale-site-topos).
-/

@[expose] public section


universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace AlgebraicGeometry.Scheme

private theorem fullAffineEtale_preservesPullbacks (S : Scheme.{u}) :
    PreservesLimitsOfShape WalkingCospan (fullAffineEtaleInclusion S) := by
  let P : ObjectProperty S.Etale := fun U => IsAffine U.left
  have : P.IsClosedUnderLimitsOfShape WalkingCospan := ⟨by
    rintro X ⟨h⟩
    let F := Etale.forget S ⋙ Over.forget S
    have (j : WalkingCospan) : IsAffine ((h.diag ⋙ F).obj j) := h.prop_diag_obj j
    exact Scheme.isAffine_of_isLimit (F.mapCone h.toLimitPresentation.cone)
      (isLimitOfPreserves F h.isLimit)⟩
  exact
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan P.ι)

/-- Source: Stacks 04HR, 021E. Proof: affine pullbacks are preserved by the full inclusion.
A finite jointly surjective affine cover is an etale cover in the small site. Apply
the target sheaf condition and the preserved-pullback comparison to every such cover.
The pretopology/coverage comparison then gives the sheaf condition for the topology.
(blueprint: lem-weil-pbc-affine-etale-inclusion-continuity_sheaf_condition) -/
theorem fullAffineEtaleInclusion_continuity_sheaf_condition (S : Scheme.{u}) :
    ∀ G : Sheaf S.smallEtaleTopology (Type (u + 1)),
      Presieve.IsSheaf
        (fullAffineEtaleTopology S)
        ((fullAffineEtaleInclusion S).op ⋙ G.obj) := by
  obtain ⟨J, hJ⟩ := fullAffineEtalePrecoverage_isPretopology S
  have := fullAffineEtale_preservesPullbacks S
  intro G
  change Presieve.IsSheaf (fullAffineEtalePrecoverage S).toGrothendieck _
  rw [← hJ]
  change Presieve.IsSheaf J.toCoverage.toPrecoverage.toGrothendieck
    ((fullAffineEtaleInclusion S).op ⋙ G.obj)
  rw [Coverage.toGrothendieck_toPrecoverage, J.toGrothendieck_toCoverage,
    Presieve.isSheaf_pretopology]
  intro U R hR
  have hR' : R ∈ fullAffineEtalePrecoverage S U := by simpa [hJ] using hR
  obtain ⟨n, V, f, rfl, hf, hsurj⟩ := hR'
  rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks]
  apply ((isSheaf_iff_isSheaf_of_type _ _).mp G.property).isSheafFor
  rw [Presieve.map_ofArrows]
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  exact hsurj x

/-- Source: Stacks 04HR (blueprint: lem-weil-pbc-affine-etale-site-topos). -/
theorem fullAffineEtaleInclusion_isContinuous (S : Scheme.{u}) :
    (fullAffineEtaleInclusion S).IsContinuous
      (fullAffineEtaleTopology S) S.smallEtaleTopology := by
  exact { op_comp_isSheaf_of_types := fullAffineEtaleInclusion_continuity_sheaf_condition S }

attribute [instance] fullAffineEtaleInclusion_isContinuous

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem fullAffineEtale_cover_refinement (S : Scheme.{u})
    (U : S.FullAffineEtale) (R : Sieve U.obj) (hR : R ∈ S.smallEtaleTopology U.obj) :
    ∃ (T : Presieve U), T ∈ fullAffineEtalePrecoverage S U ∧
      T.map (fullAffineEtaleInclusion S) ≤ R.arrows := by
  classical
  have : IsAffine U.obj.left := U.property
  obtain ⟨𝒰, hOver, hp, hle⟩ := (S.mem_smallGrothendieckTopology U.obj R).mp hR
  have : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun i => (𝒰.f i).isOpenMap)
  obtain ⟨𝒱, a, hfin, hopen⟩ := QuasiCompactCover.exists_hom 𝒰
  let := Fintype.ofFinite 𝒱.I₀
  have (j : 𝒱.I₀) : AlgebraicGeometry.Etale (𝒱.f j) := 𝒱.cover.map_prop j
  have : AlgebraicGeometry.Etale U.obj.hom := U.obj.prop
  let e := Fintype.equivFin 𝒱.I₀
  let V : Fin (Fintype.card 𝒱.I₀) → S.FullAffineEtale := fun i =>
    ⟨Scheme.Etale.mk (𝒱.f (e.symm i) ≫ U.obj.hom), by
      change IsAffine (Spec _)
      infer_instance⟩
  let f : ∀ i, V i ⟶ U := fun i =>
    ObjectProperty.homMk (MorphismProperty.Over.homMk (𝒱.f (e.symm i)))
  refine ⟨Presieve.ofArrows V f, ⟨_, V, f, rfl, ?_, ?_⟩, ?_⟩
  · intro i
    exact 𝒱.cover.map_prop (e.symm i)
  · intro x
    obtain ⟨j, y, hy⟩ := 𝒱.cover.exists_eq x
    refine ⟨e j, ?_⟩
    change ∃ y : Spec (𝒱.X (e.symm (e j))), (𝒱.f (e.symm (e j))) y = x
    rw [e.symm_apply_apply]
    exact ⟨y, hy⟩
  · rw [Presieve.map_ofArrows]
    rintro Y g ⟨i⟩
    let j := e.symm i
    let b : (fullAffineEtaleInclusion S).obj (V i) ⟶
        (𝒰.X (a.s₀ j)).asOverProp S (hp (a.s₀ j)) :=
      MorphismProperty.Over.homMk (a.h₀ j) (by
        change a.h₀ j ≫ (𝒰.X (a.s₀ j) ↘ S) = 𝒱.f j ≫ U.obj.hom
        calc
          _ = a.h₀ j ≫ 𝒰.f (a.s₀ j) ≫ U.obj.hom := by
            congr 1
            exact (CategoryTheory.comp_over (𝒰.f (a.s₀ j)) S).symm
          _ = _ := by rw [← Category.assoc]; exact congrArg (· ≫ U.obj.hom) (a.w₀ j))
    have hb : b ≫ (𝒰.f (a.s₀ j)).asOverProp S =
        (fullAffineEtaleInclusion S).map (f i) := by
      apply MorphismProperty.Over.Hom.ext
      exact a.w₀ j
    rw [← hb]
    exact R.downward_closed (hle _ _ ⟨a.s₀ j⟩) b

private theorem fullAffineEtale_image_cover (S : Scheme.{u}) (V : S.Etale) :
    ∃ (I : Type u) (U : I → S.FullAffineEtale)
      (f : ∀ i, (fullAffineEtaleInclusion S).obj (U i) ⟶ V),
      Sieve.ofArrows _ f ∈ S.smallEtaleTopology V := by
  let E := (AffineEtale.Spec S).oneHypercoverDenseData.{u}
    (AffineEtale.topology S) S.smallEtaleTopology V
  let U : E.I₀ → S.FullAffineEtale := fun i =>
    ⟨(AffineEtale.Spec S).obj (E.X i), by change IsAffine (Spec _); infer_instance⟩
  exact ⟨E.I₀, U, E.f, E.mem₀⟩

private theorem fullAffineEtale_cover_dense (S : Scheme.{u}) :
    (fullAffineEtaleInclusion S).IsCoverDense S.smallEtaleTopology := by
  constructor
  intro V
  obtain ⟨I, U, f, hf⟩ := fullAffineEtale_image_cover S V
  apply S.smallEtaleTopology.superset_covering _ hf
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro W g ⟨i⟩
  exact Presieve.in_coverByImage _ (f i)

set_option backward.isDefEq.respectTransparency false in
private theorem fullAffineEtale_topology_eq_induced (S : Scheme.{u}) :
    fullAffineEtaleTopology S =
      (fullAffineEtaleInclusion S).inducedTopology S.smallEtaleTopology := by
  have := fullAffineEtale_cover_dense S
  have : (fullAffineEtaleInclusion S).Full :=
    inferInstanceAs (ObjectProperty.ι (fun U : S.Etale => IsAffine U.left)).Full
  have : (fullAffineEtaleInclusion S).Faithful :=
    inferInstanceAs (ObjectProperty.ι (fun U : S.Etale => IsAffine U.left)).Faithful
  apply le_antisymm
  · rw [Functor.le_inducedTopology_iff]
    infer_instance
  · intro U R hR
    rw [Functor.mem_inducedTopology_iff_of_isCoverDense] at hR
    obtain ⟨T, hT, hle⟩ := fullAffineEtale_cover_refinement S U _ hR
    have hTR : T ≤ R.arrows := by
      intro V f hf
      have h := hle _ _ (Presieve.map.of hf)
      obtain ⟨W, g, i, hg, hi⟩ := h
      have hfac : (fullAffineEtaleInclusion S).preimage i ≫ g = f := by
        apply (fullAffineEtaleInclusion S).map_injective
        simpa using hi.symm
      rw [← hfac]
      exact R.downward_closed hg _
    exact (fullAffineEtaleTopology S).superset_covering
      ((Sieve.generate_le_iff _ _).mpr hTR) (Precoverage.generate_mem_toGrothendieck hT)

private theorem fullAffineEtale_dense_subsite (S : Scheme.{u}) :
    (fullAffineEtaleInclusion S).IsDenseSubsite
      (fullAffineEtaleTopology S) S.smallEtaleTopology := by
  have := fullAffineEtale_cover_dense S
  have : (fullAffineEtaleInclusion S).Full :=
    inferInstanceAs (ObjectProperty.ι (fun U : S.Etale => IsAffine U.left)).Full
  have : (fullAffineEtaleInclusion S).Faithful :=
    inferInstanceAs (ObjectProperty.ι (fun U : S.Etale => IsAffine U.left)).Faithful
  rw [fullAffineEtale_topology_eq_induced]
  infer_instance

private theorem fullAffineEtale_oneHypercover_dense (S : Scheme.{u}) :
    (fullAffineEtaleInclusion S).IsOneHypercoverDense.{u}
      (fullAffineEtaleTopology S) S.smallEtaleTopology := by
  have := fullAffineEtale_cover_dense S
  have : (fullAffineEtaleInclusion S).Full :=
    inferInstanceAs (ObjectProperty.ι (fun U : S.Etale => IsAffine U.left)).Full
  have : (fullAffineEtaleInclusion S).Faithful :=
    inferInstanceAs (ObjectProperty.ι (fun U : S.Etale => IsAffine U.left)).Faithful
  have hd : (fullAffineEtaleInclusion S).IsDenseSubsite
      (fullAffineEtaleTopology S) S.smallEtaleTopology := by
    rw [fullAffineEtale_topology_eq_induced]
    infer_instance
  exact Functor.IsOneHypercoverDense.of_hasPullbacks (fullAffineEtale_image_cover S)

/-- Source: Stacks 04HR. Proof: the full inclusion is a dense subsite for the finite
affine topology, by finite affine refinement. Small affine image covers make it
one-hypercover dense in universe u. Apply Mathlib
`Functor.isEquivalence_of_isOneHypercoverDense` with coefficients Type u.
(blueprint: lem-weil-pbc-affine-etale-sets_equivalence) -/
theorem fullAffineEtale_sets_equivalence (S : Scheme.{u}) :
    ((fullAffineEtaleInclusion S).sheafPushforwardContinuous (Type u)
      (fullAffineEtaleTopology S) S.smallEtaleTopology).IsEquivalence := by
  have := fullAffineEtale_oneHypercover_dense S
  have := fullAffineEtale_dense_subsite S
  exact Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _




end AlgebraicGeometry.Scheme
