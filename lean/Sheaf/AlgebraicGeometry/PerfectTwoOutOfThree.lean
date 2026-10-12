/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.Paper.AffineProjectiveComplexDerivedHom

/-! # Two out of three for perfect complexes on a scheme

Source: Stacks Project, Cohomology of Sheaves, Lemma 20.49.7, Tag 08CR
(blueprint: lem-pc-perfect-two-out-of-three).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme

/-- In a distinguished triangle of `D(𝒪_X)`, any two perfect terms force the third to be
perfect. Source: Stacks Project, Cohomology of Sheaves, Lemma 20.49.7, Tag 08CR
(blueprint: lem-pc-perfect-two-out-of-three).

Proof: By `def-pc-perfect-complex`, intersect and refine the local covers of the two
perfect terms to a common affine cover. Restriction is exact and preserves cone triangles
(`def-weil-abstract-derived-category`). On each affine open, Tag 08EB represents both
perfect terms by bounded complexes of finite projective modules.

If the first two terms are perfect, `lem-pc-affine-qcoh-derived-equivalence` lifts their
arrow to the module derived category, and `lem-sc-affine-projective-complex-derived-hom`
represents it by a chain map. Its cone is bounded, with terms the direct sums of the second
complex's terms and shifted terms of the first, hence finite projective. Sheafification
commutes with that cone. TR3 (`def-weil-triangulated-category`) extends the first two
isomorphisms to a triangle morphism; `lem-sf-triangle-morphism-iso` makes the third component
an isomorphism. Thus the third term is locally represented by a strictly perfect complex.

If the last two terms are perfect, rotate the triangle by TR2 and apply the first case;
then shift back. If the first and last terms are perfect, rotate backwards, apply the first
case to the shifted last term and the first term, and obtain the middle term. Shifts preserve
bounded finite projective complexes. Finally the local conclusions on the common affine
cover imply perfectness on `X` by `def-pc-perfect-complex`. -/
theorem isPerfect_two_out_of_three (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (T : Triangle (schemeDerivedCategory X)) (hT : T ∈ distTriang (schemeDerivedCategory X)) :
    (IsPerfect X T.obj₁ → IsPerfect X T.obj₂ → IsPerfect X T.obj₃) ∧
      (IsPerfect X T.obj₂ → IsPerfect X T.obj₃ → IsPerfect X T.obj₁) ∧
      (IsPerfect X T.obj₁ → IsPerfect X T.obj₃ → IsPerfect X T.obj₂) := by
  sorry

end AlgebraicGeometry.Scheme
