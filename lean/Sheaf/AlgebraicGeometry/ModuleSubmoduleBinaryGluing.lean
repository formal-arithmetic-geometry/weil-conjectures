/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent

/-! # Gluing a submodule with the ambient module on two opens

Source: Stacks Project, Properties, Lemma 01PF, binary gluing step.
(blueprint: lem-weil-pbc-module-submodule-binary-gluing).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- Glue a finite-type submodule on V to the whole module on W when its inclusion
is an isomorphism on the overlap. No compactness or affineness is required.

Source: Stacks Project, Properties, Lemma 01PF (label lemma-extend), reduction
from a union to its affine member, gluing along the common value on the overlap.
https://stacks.math.columbia.edu/tag/01PF
(blueprint: lem-weil-pbc-module-submodule-binary-gluing).

Proof: Since ι is mono, identify Q with its image subsheaf of H on V. For every
open T contained in W union V, define G(T) to be the submodule of H(T) consisting
of sections whose restriction to T intersect V belongs to this image subsheaf.
Restriction maps preserve this condition. To verify the sheaf axiom, glue a
compatible family in H; their restrictions to V glue in the image subsheaf,
so the glued section again lies in G. The inclusions G(T) -> H(T) give a
monomorphism φ. On an open contained in V, the image condition identifies G
with Q. On an open contained in W, its intersection with V lies in W intersect V,
where ι is an isomorphism, so the condition imposes no restriction: G is H there.
Thus the restriction of φ to W is an isomorphism. Local presentations for Q on V
and H on W give local presentations of G on the covering W,V, proving
quasi-coherence. Their finite generating families give finite generating
families for G on the same covering, proving finite type. The sectionwise
construction works also for empty opens or disjoint W,V, and requires neither
quasi-separatedness nor compactness. -/
theorem exists_submodule_binary_gluing
    (X : Scheme.{u}) (W V : X.Opens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [H.IsQuasicoherent]
    [(H.over W).IsFiniteType]
    (Q : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    [Q.IsQuasicoherent] [Q.IsFiniteType] (ι : Q ⟶ H.over V) [Mono ι]
    [IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (show W ⊓ V ≤ V from inf_le_right))).map ι)] :
    ∃ G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (W ⊔ V)),
      G.IsQuasicoherent ∧ G.IsFiniteType ∧ ∃ (φ : G ⟶ H.over (W ⊔ V)),
        Mono φ ∧ IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE (show W ≤ W ⊔ V from le_sup_left))).map φ) := by sorry

end AlgebraicGeometry.Scheme.Modules
