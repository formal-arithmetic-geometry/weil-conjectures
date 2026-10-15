/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # The zero locus of an étale section is Zariski open

Source: Stacks Project, Tag 04FR (blueprint: lem-sc-etale-section-zero-open).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The zero locus theorem for a section of an abelian sheaf on the small étale site.
Source: Stacks Project, Tag 04FR, clauses (1)--(3) (blueprint: lem-sc-etale-section-zero-open).

Proof:
1. Form the union of the open subschemes where `s` restricts to zero. Open immersions
are étale by `lem-weil-pbc-etale-composition-cancellation`, so these are site objects.
The sheaf condition (`def-weil-pbc-abelian-etale-sheaves`) gives zero on this union,
including an empty union; maximality follows from the construction.
2. Every site arrow is étale by cancellation. Its image is open by
`lem-weil-pbc-etale-morphism-open-map`, and the map onto that image is a singleton
étale cover. Sheaf separatedness descends vanishing to the image. Conversely,
containment in the union gives factorization and hence zero restriction.
3. Compute the geometric stalk (`def-weil-pbc-geometric-stalks`) using a small
cofinal family of affine pointed neighbourhoods. Representatives exist by
`lem-weil-pbc-affine-etale-essentially-small-cover`; an affine open around the lifted
point refines any neighbourhood. Cofilteredness follows from
`lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`, and
`lem-weil-pbc-colimit-initial-full-subcategory` identifies the small colimit and its
coprojections with the stalk. Restrict `s` to a pointed affine refinement of `V`.
4. If the germ is zero, regard the abelian groups as integer modules and apply
`lem-weil-pbc-filtered-colimit-modules-elementwise`: some pointed refinement has zero
restriction. Its image lies in the union by step 2, so the geometric point lies there.
5. Conversely, a geometric point in the union factors through its open immersion.
The stalk coprojections identify the germ of `s` with that of its zero restriction.
-/
theorem etale_section_zero_open
    (T : Scheme.{u})
    (F : Sheaf (T.smallEtaleTopology) AddCommGrpCat.{u + 1})
    (V : T.Etale)
    (s : (F.1.obj (Opposite.op V) : AddCommGrpCat.{u + 1}).carrier)
    : ∃ (W : T.Etale) (i : W ⟶ V),
        IsOpenImmersion i.left ∧
        (∀ (V' : T.Etale) (h : V' ⟶ V),
          (F.1.map h.op) s = 0 ↔ Set.range h.left ⊆ Set.range i.left) ∧
        (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
          (v : Spec (.of Ω) ⟶ V.left),
          (pointSmallEtale (v ≫ V.hom)).toPresheafFiber V (Over.homMk v) F.1 s = 0 ↔
            ∃ (y : Spec (.of Ω) ⟶ W.left), y ≫ i.left = v) := by
  sorry

end AlgebraicGeometry.Scheme
