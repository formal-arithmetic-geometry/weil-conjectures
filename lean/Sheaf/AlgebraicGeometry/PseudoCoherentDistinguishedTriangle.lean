/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex

/-! # Pseudo-coherence is closed under distinguished triangles

Source: Stacks Project, Cohomology of Sheaves, Tag 08CD,
`lemma-cone-pseudo-coherent`, part (2) for every integer m
(blueprint: lem-pc-pseudo-coherent-distinguished-triangle).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme

/-- In a distinguished triangle in `D(𝒪_Y)`, pseudo-coherence of the first and third
objects implies pseudo-coherence of the second.

Source: Stacks Project, Cohomology of Sheaves, Tag 08CD, part (2) for every m
(blueprint: lem-pc-pseudo-coherent-distinguished-triangle).

Proof:
1. By `def-pur-pseudo-coherent-complex`, choose local bounded-above finite-free models
   for the first and third objects and refine to a common affine open cover. Restriction
   is exact, so the restricted triangles remain distinguished. It suffices to construct
   a bounded-above finite-free model for the middle object on each of these opens.
2. On an affine open U = Spec R the finite-free models come from complexes P_A and P_C
   of finite free R-modules. Rotate to C[-1] → A → B → C using
   `def-weil-triangulated-category`. Transfer the first map to D(R) using
   `lem-pc-affine-qcoh-derived-equivalence`. The source P_C[-1] is K-projective by
   `lem-sc-bounded-above-projective-kprojective`, so its derived map is represented by
   a chain map g : P_C[-1] → P_A (`def-weil-abstract-derived-category`).
3. The cone of g has degree-r term P_A^r ⊕ P_C^r, hence is bounded above and finite free.
   Its cone triangle is distinguished (`def-weil-abstract-derived-category`). The
   triangulated affine equivalence transports this triangle back. Its third object is
   isomorphic to B on U, by TR3 and the five lemma on Hom
   (`def-weil-triangulated-category`). Locality (`def-pur-pseudo-coherent-complex`)
   therefore gives pseudo-coherence of B on Y. -/
theorem isPseudoCoherent_of_distinguished_triangle (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (T : Triangle (schemeDerivedCategory Y))
    (hT : T ∈ distTriang (schemeDerivedCategory Y))
    (hA : IsPseudoCoherent Y T.obj₁) (hC : IsPseudoCoherent Y T.obj₃) :
    IsPseudoCoherent Y T.obj₂ := by
  sorry

end AlgebraicGeometry.Scheme
