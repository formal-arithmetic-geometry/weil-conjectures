/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence
public import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.CategoryTheory.SiteCechVanishingCriterion
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison

/-! # Vanishing for fppf modules zero on flat locally finitely presented tests

Source: Stacks Project, Descent, Tags 06ZL and 0755(1), fppf case;
Cohomology on Sites, Tags 03F9 and 03FD
(blueprint: lem-sfb-fppf-flat-lfp-zero-cohomology).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Enough injectives for modules over the actual big-fppf structure sheaf, in a
common universe containing the site. This is the existing Grothendieck-category
construction, with no additional geometric hypothesis or chosen abelian structure.

Source: Stacks Project, Injectives, Tags 079Q and 079H; Descent, Tag 0755
(blueprint: lem-sfb-fppf-flat-lfp-zero-cohomology). -/
noncomputable instance fppfStructureModuleEnoughInjectives (S : Scheme.{u}) :
    EnoughInjectives (ringedSiteModules.{max (u + 1) w} (sfbFppfRings S)) :=
  @IsGrothendieckAbelian.enoughInjectives _ _ _
    (SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u, w}
      (fppfTopology.over S) (sfbFppfRings S))

/-- A structure-module sheaf with zero sections on every flat locally finitely
presented object has zero derived evaluation on all those objects, including the
identity. The right derived functor here resolves in module sheaves, before
forgetting to abelian sheaves and evaluating. No quasi-coherence, affineness, or
condition on sections outside this class is required.

Source: Stacks Project, Descent, Tag 0755(1), with Tag 06ZL;
Cohomology on Sites, Tags 03F9 and 03FD
(blueprint: lem-sfb-fppf-flat-lfp-zero-cohomology).

Proof (the node's four steps):
1. Let B be the flat locally finitely presented objects over S and Cov all fppf
   coverings of them. Covering members lie in B by lem-pc-flat-compose and
   lem-sbc-locally-finite-presentation-composition. Every nonempty iterated fibre
   product lies in B by induction, using lem-weil-pbc-flat-morphism-base-change
   and clause (3) of lem-weil-pbc-qcqs-morphism-permanence for its projections.
   Every covering refines itself, so Cov is cofinal, without any qcqs hypothesis.
2. For the underlying abelian sheaf, every factor of every term of the Cech
   complex of a covering in Cov is zero by the hypothesis. By
   def-weil-pbc-site-cech-complex these terms are products of zero groups, hence
   zero, even for an empty covering. All Cech cohomology groups are zero.
3. Apply lem-weil-pbc-site-cech-vanishing-criterion to obtain positive abelian
   cohomology vanishing on B. By lem-weil-pbc-ring-sheaves-grothendieck and
   lem-sp-grothendieck-enough-injectives the module category has enough injectives.
   The comparison lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison
   identifies module derived evaluation with abelian cohomology. It does not
   require that forgetting scalars preserve injectivity.
4. In degree zero the same comparison identifies derived evaluation with P(V),
   which is zero by hypothesis. The identity of S is flat and locally finitely
   presented, giving the final assertion, also for the empty scheme.
-/
theorem fppf_flat_lfp_zero_cohomology (S : Scheme.{u})
    (P : ringedSiteModules.{max (u + 1) w} (sfbFppfRings S))
    (hP : ∀ V : Over S, Flat V.hom → LocallyOfFinitePresentation V.hom →
      Subsingleton (P.val.obj (op V))) :
    (∀ V : Over S, Flat V.hom → LocallyOfFinitePresentation V.hom → ∀ q : ℕ,
      IsZero (((SheafOfModules.toSheaf (sfbFppfRings S) ⋙
        sheafToPresheaf (fppfTopology.over S) AddCommGrpCat.{max (u + 1) w} ⋙
          (CategoryTheory.evaluation (Over S)ᵒᵖ AddCommGrpCat.{max (u + 1) w}).obj
            (op V)).rightDerived q).obj P)) ∧
    (∀ q : ℕ,
      IsZero (((SheafOfModules.toSheaf (sfbFppfRings S) ⋙
        sheafToPresheaf (fppfTopology.over S) AddCommGrpCat.{max (u + 1) w} ⋙
          (CategoryTheory.evaluation (Over S)ᵒᵖ AddCommGrpCat.{max (u + 1) w}).obj
            (op (Over.mk (𝟙 S)))).rightDerived q).obj P)) := by
  sorry

end AlgebraicGeometry.Scheme
