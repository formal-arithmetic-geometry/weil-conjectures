/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleGraphSectionExtensionMap
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleInverseImageModulesExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Linearity of extension of graph sections over the constant ring sheaf

Source: Stacks Project, Tags 03DI and 0F4L
(blueprint: lem-weil-pbc-etale-graph-section-extension-map-linear).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The sum presheaf and graph-extension comparison are linear over the constant ring sheaf.
Source: Stacks Project, Tag 03DI, proof, first paragraph, and Tag 0F4L, proof
(blueprint: lem-weil-pbc-etale-graph-section-extension-map-linear).

The immediately applied lambda names the constant ring sheaves, localization, base change,
its graph unit, and the underlying sum presheaf. The second lambda names the direct image
with scalars restricted through the canonical ring map and the maps theta. The isomorphism
`i` identifies the underlying presheaf of `PM` with the existing Kan-extension sum presheaf;
its naturality identifies maps on sheaves with the sum of their maps on summands. The
condition on `c` characterizes precisely the comparison of the graph-extension dependency.

Proof, following the node's six steps:
1. The graph and base-change maps are morphisms on the small etale sites, by
lem-weil-pbc-etale-graph-section-extension-map and def-weil-pbc-etale-site. Compose
restriction along the graph with gamma of prop-weil-pbc-inverse-image-modules-exact.
This is a ring map (def-weil-pbc-constant-sheaf and def-weil-pbc-direct-image).
2. Naturality of the unit of localization/base change is the graph identity; alternatively
compare its two projections using def-pc-fibre-product.
3. Naturality of gamma and that identity give compatibility of theta with restriction.
4. Restrict scalars through theta on each summand. Compatibility in step 3 and the
semilinearity of the restrictions of M give semilinear restrictions on the direct sum,
including when several indices merge. This is a presheaf of modules; summing the
components of a module-sheaf morphism gives a morphism of these presheaves
(def-weil-sheaf-of-modules-category, def-weil-pbc-etale-sum-extension,
def-weil-presheaf-modules-sheafification).
5. Multiply the extension of s by gamma(f). Its graph restriction is theta(f) times s;
its restriction off the graph is zero, by semilinearity. Uniqueness of extension in
lem-weil-pbc-etale-graph-section-extension-map identifies it with the extension of theta(f)s.
6. Sum step 5 over finitely many summands to obtain linearity of the comparison.
Its naturality in the site object and in M is that of the graph-extension dependency.
The target module structure is restriction of scalars through gamma, as in
prop-weil-pbc-inverse-image-modules-exact and def-weil-pbc-direct-image.
-/
theorem etale_graph_section_extension_map_linear
    {X U : Scheme.{u}} (π : U ⟶ X) [IsFinite π] [Etale π]
    (Λ : Type (u + 1)) [CommRing Λ] :
    let L := MorphismProperty.Over.map (P := @Etale) ⊤ (inferInstance : Etale π)
    let P := sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙ L.op.lan
    let D := Etale.lowerStar (ModuleCat.{u + 1} Λ) π ⋙
      sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    ∃ c : P ⟶ D,
      ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (V : X.Etaleᵒᵖ) (f : Λ) (s : ((P.obj M).obj V)),
        (c.app M).app V (f • s) = f • (c.app M).app V s := by
  sorry

end AlgebraicGeometry
