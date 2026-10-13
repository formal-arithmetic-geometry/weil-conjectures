/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.AlgebraicGeometry.Coherent

import Sheaf.Topology.GlueSheavesOfModules

/-! # Gluing a finite presentation and its map across two opens

Source: Stacks Project, Properties, Lemma 01PI, gluing paragraph.
(blueprint: lem-weil-pbc-module-finite-presentation-binary-gluing).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Glue the old module on W to a finitely presented replacement on V using the
replacement map as the overlap identification. This constructs only a module on
W union V, with a map to the restriction of H.

Source: Stacks Project, Properties, Lemma 01PI, second paragraph of the proof
(https://stacks.math.columbia.edu/tag/01PI), and sheaf-module descent, Tag 00AK.
(blueprint: lem-weil-pbc-module-finite-presentation-binary-gluing).

Proof: Restrict the map j to W intersect V. It is an isomorphism by hypothesis.
Identify its target with the restriction of H on W by the canonical iterated
restriction isomorphisms. Glue H on W and E on V using this identification.
For the two-open cover, all cocycle equations reduce to the inverse identities
for the overlap isomorphism and identity maps. Sheaf-module descent produces G
on W union V with the prescribed local identifications. The identity map to H
on W and j on V agree on the overlap by the choice of identification, so glue
to a map phi. Finite presentation is local and invariant under isomorphism;
thus G is finitely presented. The restriction of phi to W is the prescribed
identification with H on W and therefore is an isomorphism. Empty opens and
identical opens cause no exception: the same two-open descent applies. This
step does not construct any affine replacement and needs no compactness,
quasi-separatedness, affineness, or quasi-coherence hypotheses. -/
theorem exists_finitePresentation_binary_gluing
    (X : Scheme.{u}) (W V : X.Opens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [(H.over W).IsFinitePresentation]
    (E : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    [E.IsFinitePresentation] (j : E ⟶ H.over V)
    [IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (show W ⊓ V ≤ V from inf_le_right))).map j)] :
    ∃ G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (W ⊔ V)),
      G.IsFinitePresentation ∧ ∃ (φ : G ⟶ H.over (W ⊔ V)),
        IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE (show W ≤ W ⊔ V from le_sup_left))).map φ) := by sorry

end AlgebraicGeometry.Scheme.Modules
