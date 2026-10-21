/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Sheaf.CategoryTheory.SheafTensor
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Sheaf.Paper.CohomologyInWeakSerreSubcategory

/-!
# Bounded constructible derived objects with weak Serre coefficients

Source: Weil conjectures blueprint, `sec-proetale-coefficients`,
`sk-def-sfb-bounded-constructible/_section.md`, with the node's reviewed weak Serre
correction; Stacks Project, Tags 06UQ and 0754
(blueprint: sk-def-sfb-bounded-constructible).

The object predicate `AlgebraicGeometry.ProEtale.boundedConstructible`, the category
`AlgebraicGeometry.ProEtale.BoundedConstructible`, and the membership characterization
`AlgebraicGeometry.ProEtale.mem_boundedConstructible_iff` are imported unchanged.
They use ordinary derived module objects, finite-stratification constructibility,
and ambient morphisms, with no derived completeness condition.
-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Bounded complexes with constructible internal-module cohomology form a full
triangulated subcategory provided the constructible modules form a weak Serre class.
The full subcategory, its shifts, and its distinguished triangles are inherited from
`DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)`.

Source: blueprint `sk-def-sfb-bounded-constructible`, reviewed statement and proof steps
1--3; Stacks Project, Tag 06UQ, `lemma-cohomology-in-serre-subcategory`, with closure
conditions expanded as in Tag 0754 (blueprint: sk-def-sfb-bounded-constructible).

Proof:
1. By `lem-weil-pbc-sheaf-tensor-closed` the small pro-etale sheaf category is abelian
with additive closed tensor. Tensoring with R preserves finite colimits, so
`lem-sfb-modobj-abelian` makes its internal module category abelian. Its ordinary
unbounded derived category and cohomology functors are those of
`def-weil-abstract-derived-category`. The existing `boundedConstructible R` is boundedness
intersected with constructibility of every cohomology module. Constructibility here is
exactly `def-sfb-constructible-module`: finite strata with locally finitely presented
module pullbacks. By `def-weil-pbc-bounded-derived-subcategories` boundedness is vanishing
outside a finite interval; replacing bounds by their minimum and maximum orders them.
2. The existing `BoundedConstructible R` is the full subcategory of this predicate,
so its morphisms, identities and compositions are inherited from the ordinary derived
category. Its object predicate contains no derived completeness requirement.
3. Apply `lem-sbc-cohomology-in-weak-serre-subcategory` to the constructible-module
predicate. The five hypotheses below give zero, isomorphisms, kernels, cokernels and
extensions, exactly its hypotheses. Its bounded intersection is triangulated with
inherited shifts and distinguished triangles. Commutativity of intersection identifies
that predicate with `boundedConstructible R`.
-/
lemma isTriangulated_boundedConstructible_of_weakSerre
    {A : Type u'} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) A)
    [MonObj R] [IsCommMonObj R]
    [ObjectProperty.ContainsZero (IsConstructibleModuleObject R)]
    [ObjectProperty.IsClosedUnderIsomorphisms (IsConstructibleModuleObject R)]
    [ObjectProperty.IsClosedUnderKernels (IsConstructibleModuleObject R)]
    [ObjectProperty.IsClosedUnderCokernels (IsConstructibleModuleObject R)]
    [ObjectProperty.IsClosedUnderExtensions (IsConstructibleModuleObject R)] :
    (boundedConstructible R).IsTriangulated := by
  change (DerivedCategory.TStructure.t.bounded ⊓
    DerivedCategory.homologyProperty (IsConstructibleModuleObject R)).IsTriangulated
  infer_instance

end AlgebraicGeometry.ProEtale
