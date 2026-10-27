/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.Topology.ModuleLocalModelGluingData
import WeilConjectures.Topology.GlueSheavesOfModules

/-!
# A set of effective gluing data for prescribed local module families

Source: Stacks Project, Modules, Tag 01BC, proof of
`lemma-set-isomorphism-classes-finite-type-modules`; Sheaves, Tags 00AL and 00AM.
(blueprint: lem-weil-pbc-module-local-model-gluing-data-set)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- The gluing data form a small set and admit a simultaneous family of effective realizations,
with their prescribed local identifications and transition equations.

Source: Stacks Project, Modules, Tag 01BC, proof of the set-of-isomorphism-classes lemma.
(blueprint: lem-weil-pbc-module-local-model-gluing-data-set)

Proof:
1. By def-weil-sheaf-of-modules-category, a morphism is a family of linear section maps.
   Its naturality and linearity are predicates on a product of function sets. Isomorphisms
   are pairs of morphisms satisfying the inverse equations, hence are also small.
2. Subsets of `Opens X`, their label families, and their transition families form a small
   dependent sum of products. The covering and cocycle conditions cut out its subset
   `ModuleLocalModelGluingData X I B`, which therefore lies in the same universe.
3. For each datum apply clause (2) of lem-weil-pbc-glue-sheaves-of-modules with its cover,
   labels, and overlap isomorphisms. The cocycle with all indices equal, followed by
   cancellation of the invertible transition, gives the diagonal identity. The theorem
   supplies a global module and the local isomorphisms with exactly the displayed equation.
4. In an ambient universe encode all possible module sheaves by their section assignments,
   operations and restriction maps, with the axioms as predicates. For each datum the set
   of these encodings together with comparison isomorphisms is nonempty by Step 3. Their
   disjoint union over the small set of data is a set; choice selects the family and its
   comparisons simultaneously. For an empty data set these are empty families. -/
theorem module_local_model_gluing_data_set (X : RingedSpace.{u}) (I : Opens X → Type u)
    (B : ∀ U : Opens X, I U → ringedSiteModules.{u} ((moduleRings X).over U)) :
    Small.{u} (ModuleLocalModelGluingData X I B) ∧
      ∃ (Φ : ModuleLocalModelGluingData X I B → ringedSiteModules.{u} (moduleRings X))
        (θ : ∀ (d : ModuleLocalModelGluingData X I B) (U : d.cover),
          (Φ d).over U.val ≅ B U.val (d.label U)),
        ∀ (d : ModuleLocalModelGluingData X I B) (U V : d.cover) (W : Opens X)
          (hU : W ≤ U.val) (hV : W ≤ V.val),
          (θ d U).hom.val.app (op (Over.mk (homOfLE hU))) ≫
              (d.transition U V).hom.val.app (op (Over.mk (homOfLE (le_inf hU hV)))) =
            (θ d V).hom.val.app (op (Over.mk (homOfLE hV))) := by
  classical
  refine ⟨inferInstance, ?_⟩
  have effective (d : ModuleLocalModelGluingData X I B) :=
    (glue_sheaves_of_modules.{u, u, u} X d.cover (fun U ↦ U.val) d.isCover).2.2
      (fun U ↦ B U.val (d.label U)) d.transition d.cocycle
  choose Φ θ hθ using effective
  exact ⟨Φ, θ, hθ⟩

end AlgebraicGeometry
