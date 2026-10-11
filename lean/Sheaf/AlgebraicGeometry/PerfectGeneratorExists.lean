/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.AlgebraicGeometry.DerivedCategory
import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.CategoryTheory.WeakTriangulatedGenerator
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

/-! # Existence of a single perfect generator

Source: literature/stacks-project/derived-categories-of-schemes.tex, Tag 09IS
(blueprint: lem-pc-perfect-generator-exists).
-/

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For a quasi-compact and quasi-separated scheme, a single perfect complex generates the
quasi-coherent derived category. Source: Stacks Project, Tag 09IS
(blueprint: lem-pc-perfect-generator-exists).

Proof:
1. On an affine scheme, the structure sheaf is a perfect weak generator:
`lem-pc-perfect-generation-affine-base` detects zero objects through all shifted Hom groups.
2. For a union of a quasi-compact open with an affine open,
`lem-pc-perfect-generation-open-induction-step` extends a perfect generator and adjoins a
perfect Koszul object supported on the complement. Their finite direct sum is perfect and
has quasi-coherent cohomology, and it weakly generates the union.
3. Apply the qcqs induction principle `lem-sc-invert-s-cohomology-induction` to the affine
case and this union step to obtain a single perfect generator on X.
4. Quasi-coherent cohomology is stable under shifts and cones and contains zero, so its
full subcategory inherits the triangulated structure, and its direct sums are those of
`D(𝒪_X)`; so a triangulated, retract-closed, sum-closed subcategory of `D(𝒪_X)` meets
`D_QCoh(X)` in such a subcategory of `D_QCoh(X)`. Arbitrary direct sums exist by
`lem-pc-derived-qcoh-direct-sums`; the perfect generator is compact by
`lem-pc-perfect-object-compact`. Apply `lem-pc-compact-generators-build-objects` (Tag 09SN)
to its singleton family: every object is a homotopy colimit of successive cones of sums of
shifts of the generator. Each such object belongs to every triangulated, retract-closed
subcategory closed under arbitrary direct sums and containing the generator. Thus that
subcategory contains every object. -/
theorem exists_perfect_generator (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    ∃ P : schemeDerivedCategory X, Scheme.IsPerfect X P ∧ schemeDerivedQCohProperty X P ∧
      (∀ E : schemeDerivedQCohCategory X,
        IsZero E.obj ↔ ∀ n : ℤ, Subsingleton (P⟦n⟧ ⟶ E.obj)) ∧
      ∀ Q : ObjectProperty (schemeDerivedCategory X),
        Q.IsTriangulated → Q.IsStableUnderRetracts →
        (∀ I : Type u, Q.IsClosedUnderColimitsOfShape (Discrete I)) →
        Q P → ∀ E : schemeDerivedQCohCategory X, Q E.obj := by
  sorry

end AlgebraicGeometry
