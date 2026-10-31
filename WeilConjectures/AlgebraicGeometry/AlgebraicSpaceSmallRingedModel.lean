/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import WeilConjectures.CategoryTheory.DenseSubsiteModuleExtension

/-! # A small affine étale model of an algebraic-space ringed topos

Source: Stacks Project, Properties of Spaces, Tags 03ED and 03G7; Sites,
comparison lemma, Tag 039Z (blueprint: def-sfb-space-small-ringed-model).

Restriction to a small skeleton of affine étale charts preserves the original module
universe. All ring sections are the actual regular functions of the chart schemes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Affine objects in the existing small étale site.
Source: Stacks, Tag 03ED (blueprint: def-sfb-space-small-ringed-model). -/
abbrev AffineEtaleCharts {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  ObjectProperty.FullSubcategory (fun T : X.EtaleSite ↦ IsAffine (X.etaleForget.obj T))

/-- Affine étale charts have a small skeleton in the original scheme universe.
Source: Stacks, Tags 03ED and 03G7 (blueprint: def-sfb-space-small-ringed-model).
Proof: choose a scheme atlas and its affine open cover. Affine étale schemes over
these affines have a small skeleton, being finitely presented algebras. Descent data
on the overlaps are sets in the same universe. Every affine étale chart is obtained
from such data, and maps are determined on the cover. This bounds the isomorphism
classes and the Hom sets in universe u, including the empty chart. -/
@[instance] theorem affineEtaleCharts_essentiallySmall
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    EssentiallySmall.{u} X.AffineEtaleCharts := by
  sorry

/-- The standard small model of the affine-chart category.
Source: Stacks, Tag 03ED (blueprint: def-sfb-space-small-ringed-model). -/
abbrev SmallEtaleModel {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  SmallModel.{u} X.AffineEtaleCharts

/-- The actual affine charts underlying the small model.
Source: Stacks, Tag 03ED (blueprint: def-sfb-space-small-ringed-model). -/
def smallEtaleInclusion {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.SmallEtaleModel ⥤ X.EtaleSite :=
  (equivSmallModel X.AffineEtaleCharts).inverse ⋙ ObjectProperty.ι _

private instance smallEtaleInclusion_full {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.smallEtaleInclusion.Full := by
  unfold smallEtaleInclusion
  infer_instance

private instance smallEtaleInclusion_faithful {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.smallEtaleInclusion.Faithful := by
  unfold smallEtaleInclusion
  infer_instance

private def affineChart {S : Scheme.{u}} (X : AlgebraicSpace S) (T : X.EtaleSite)
    (i : (X.etaleForget.obj T).affineCover.I₀) : X.AffineEtaleCharts := by
  let U := X.etaleForget.obj T
  let r : Over.mk (U.affineCover.f i ≫ T.obj.left.hom) ⟶ T.obj.left :=
    Over.homMk (U.affineCover.f i)
  have hr : IsEtale (yoneda.map r) :=
    (representable_etale_scheme_tests.2.2.2.2.2.2.2.1 _ _ r).2 (by
      change Etale (U.affineCover.f i)
      infer_instance)
  refine ⟨⟨CostructuredArrow.mk (yoneda.map r ≫ T.obj.hom),
    isEtale_comp _ _ hr T.property⟩, ?_⟩
  change IsAffine (U.affineCover.X i)
  infer_instance

private def affineChartMap {S : Scheme.{u}} (X : AlgebraicSpace S) (T : X.EtaleSite)
    (i : (X.etaleForget.obj T).affineCover.I₀) : (affineChart X T i).obj ⟶ T :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (Over.homMk ((X.etaleForget.obj T).affineCover.f i)) (by rfl))

private instance smallEtaleInclusion_coverDense {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.smallEtaleInclusion.IsCoverDense X.etaleTopology where
  is_cover T := by
    let U := X.etaleForget.obj T
    let V := fun i : U.affineCover.I₀ ↦ (affineChart X T i).obj
    let f := fun i : U.affineCover.I₀ ↦ affineChartMap X T i
    apply X.etaleTopology.superset_covering (S := Sieve.generate (Presieve.ofArrows V f))
    · apply (Sieve.generate_le_iff _ _).mpr
      rintro W g ⟨i⟩
      let e := equivSmallModel X.AffineEtaleCharts
      let A := affineChart X T i
      exact ⟨⟨e.functor.obj A, (ObjectProperty.ι _).map (e.unitIso.hom.app A),
        (ObjectProperty.ι _).map (e.unitIso.inv.app A) ≫ f i, by
          rw [← Category.assoc, ← Functor.map_comp, e.unitIso.hom_inv_id_app]
          exact Category.id_comp _⟩⟩
    · apply Precoverage.generate_mem_toGrothendieck
      constructor
      · rintro W g ⟨i⟩
        change Etale (U.affineCover.f i)
        infer_instance
      · intro x
        obtain ⟨i, y, hy⟩ := U.affineCover.exists_eq x
        exact ⟨V i, f i, Presieve.ofArrows.mk i, y, hy⟩

/-- The topology induced by the existing étale topology.
Source: Stacks, Tags 03ED and 039Z (blueprint: def-sfb-space-small-ringed-model). -/
abbrev smallEtaleModelTopology {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  X.smallEtaleInclusion.inducedTopology X.etaleTopology

/-- The regular-functions presheaf on the small affine model is a sheaf.
Source: Stacks, Tags 03G7 and 039Z (blueprint: def-sfb-space-small-ringed-model).
Proof: the inclusion is continuous for the induced topology. Restrict the structure
sheaf, retaining its commutative section rings. The forgetful functor to rings
creates the sheaf equalizers, so the restricted commutative presheaf is a sheaf. -/
theorem smallStructurePresheaf_isSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Presheaf.IsSheaf X.smallEtaleModelTopology
      ((X.smallEtaleInclusion ⋙ X.etaleForget).op ⋙ Scheme.Γ) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat)
  change Presheaf.IsSheaf X.smallEtaleModelTopology
    (X.smallEtaleInclusion.op ⋙ X.structurePresheaf)
  exact Functor.op_comp_isSheaf_of_isSheaf _ _ _ _ X.structurePresheaf_isSheaf

/-- The commutative structure sheaf on the small model, with no coefficient lift.
Source: Stacks, Tag 03G7 (blueprint: def-sfb-space-small-ringed-model). -/
def smallStructureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf X.smallEtaleModelTopology CommRingCat.{u} :=
  ⟨(X.smallEtaleInclusion ⋙ X.etaleForget).op ⋙ Scheme.Γ,
    smallStructurePresheaf_isSheaf X⟩

/-- The underlying ring sheaf on the small model.
Source: Stacks, Tag 03G7 (blueprint: def-sfb-space-small-ringed-model). -/
abbrev smallStructureRings {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf X.smallEtaleModelTopology RingCat.{u} :=
  (sheafCompose X.smallEtaleModelTopology (forget₂ CommRingCat RingCat)).obj
    X.smallStructureSheaf

/-- Module sheaves on the small affine model, in exactly the original module universe.
Source: Stacks, Tags 03G7 and 0409 (blueprint: def-sfb-space-small-ringed-model). -/
abbrev SmallModules {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  ringedSiteModules.{u} X.smallStructureRings

/-- Restriction of the given module sheaves to the actual small affine charts.
The identity ring map is the equality of the regular-functions presheaves.
Source: Stacks, Tags 03G7 and 039Z (blueprint: def-sfb-space-small-ringed-model). -/
def smallModuleRestriction {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.Modules ⥤ X.SmallModules :=
  SheafOfModules.pushforward (F := X.smallEtaleInclusion) ⟨𝟙 _⟩

/-- Restriction to the affine basis is an equivalence of module categories.
Source: Stacks, Tag 039Z (blueprint: def-sfb-space-small-ringed-model).
Proof: affine open covers refine every étale chart and their overlaps. The usual
compatible-family extension from this basis is inverse to restriction, with unit
and counit the identity on every affine-chart section. Scalar actions descend with
the sections, since all scalar maps are the same regular-function restrictions.
This proves full faithfulness and essential surjectivity for modules. -/
@[instance] theorem smallModuleRestriction_isEquivalence
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.smallModuleRestriction.IsEquivalence := by
  have : X.smallEtaleInclusion.IsDenseSubsite
      X.smallEtaleModelTopology X.etaleTopology := by
    dsimp only [smallEtaleModelTopology]
    infer_instance
  exact SheafOfModules.denseRestriction_isEquivalence
    X.smallEtaleInclusion X.structureSheaf

/-- The equivalence determined by the actual restriction functor.
Source: Stacks, Tag 039Z (blueprint: def-sfb-space-small-ringed-model). -/
def smallModuleEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.Modules ≌ X.SmallModules :=
  X.smallModuleRestriction.asEquivalence

end AlgebraicGeometry.AlgebraicSpace
