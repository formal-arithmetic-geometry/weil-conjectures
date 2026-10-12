/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetSectionComparison
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # Composition calculation for étale section comparisons

Source: Stacks Project, Sites Tags 03CB and 03CC, and Étale Cohomology Tag 09YQ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The scheme-level composition calculation for two commuting triangles.

Source: Stacks Project, Sites Tags 03CB and 03CC (units of composite inverse images),
with fibre-product pasting as in Étale Cohomology Tag 09YQ.
(blueprint: lem-weil-pbc-sets-section-comparison-composition).

Proof: first substitute `h ≫ f` for `k`, and `g ≫ k` for `l`. Expand both section maps
as their adjunction units, the chosen inverse-image composition isomorphisms, and
restriction along the fibre-product pasting isomorphisms. Naturality of the `g`-unit
in the site object moves the restriction for `(h,f)` through that unit. Naturality
of the same unit in the sheaf morphism given by the `(f,h)` composition isomorphism
moves that isomorphism through the unit. Naturality of the `(k,g)` composition
isomorphism moves the resulting restriction to the last presheaf map. Apply the
associativity clause for the chosen composition isomorphisms in
`etaleSetInverseImageCompositionUnits`, for the three morphisms `f`, `h`, and `g`.
Now the `(h,g)` composition isomorphism follows the two successive units. Its unit
compatibility clause replaces those two units by the unit for `g ≫ h`, followed by
restriction along the inverse pasting map for `(g,h)`. The remaining restrictions
combine by the presheaf composition law. The associativity of fibre-product pasting,
`MorphismProperty.Over.pullbackComp_assoc`, identifies their composite with the
single pasting map for `(g ≫ h,f)`; equivalently, their projections to `U` and `V`
are the same, so pullback uniqueness identifies them. This is exactly the single
section comparison on the right. Restore `k` and `l` by equality elimination;
proof irrelevance identifies the equality witnesses. No sections are required to
exist, and none of these steps assumes a cover, directedness, or a limit cone. -/
theorem etaleSetSectionComparisonComposition
    {R S T V : Scheme.{u}} (h : T ⟶ S) (g : V ⟶ T) (f : S ⟶ R)
    (k : T ⟶ R) (l : V ⟶ R) (hk : h ≫ f = k) (hl : g ≫ k = l)
    (G : Sheaf R.smallEtaleTopology (Type (u + 1))) (U : R.Etale) :
    etaleSetSectionComparison h f k hk G U ≫
        etaleSetSectionComparison g k l hl G U =
      etaleSetSectionComparison (g ≫ h) f l
        (by rw [Category.assoc, hk, hl]) G U := by sorry

end AlgebraicGeometry
