/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Underlying modules of filtered colimits of commutative algebras

Source: Stacks Project, Algebra, Tag 00D6 (lemma-directed-colimit); the algebra version is
used implicitly in Tag 07RI (lemma-colimit-etale).
(blueprint: lem-weil-pbc-filtered-colimit-algebras-underlying-module)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CommAlgCat

/-- The underlying module of the filtered colimit `colimit F` of commutative `R`-algebras,
with the coprojections `colimit.ι F i`, satisfies the module colimit universal property.
Source: Stacks Project, Algebra, Tag 00D6 (lemma-directed-colimit), transcribed to algebras,
as used implicitly in Tag 07RI (lemma-colimit-etale).
(blueprint: lem-weil-pbc-filtered-colimit-algebras-underlying-module)

Proof, following the node's five steps:
1. By `lem-weil-pbc-filtered-colimit-algebras-elementwise`, the colimit cocone is also a ring
   colimit and every element is represented at a stage. Apply
   `lem-weil-pbc-filtered-colimit-rings-zero` to this ring colimit: two representatives
   agree exactly when their images agree at a common later object.
2. Algebra maps are additive and commute with the structure maps from `R`, hence are
   `R`-linear. The algebra cocone identities therefore give a module cocone, using
   `def-weil-pbc-category-colimit`.
3. Define the descended map on an element represented by `a` at stage `i` to be `f i a`.
   The equality criterion and compatibility of the family make this independent of
   the representative, and give the required identities on all coprojections.
4. Represent two elements at a common later object, using filteredness. Addition and
   scalar multiplication are computed there, so linearity follows from linearity of
   the stage map.
5. Every element comes from a stage. Thus any map with the required identities agrees
   with the descended map on every element, proving uniqueness and the universal property.
-/
theorem filtered_colimit_algebras_underlying_module
    {R : Type u} [CommRing R] {I : Type v} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{v} R) [HasColimit F]
    (P : Type w) [AddCommGroup P] [Module R P]
    (f : ∀ i : I, F.obj i →ₗ[R] P)
    (hf : ∀ (i j : I) (a : i ⟶ j), (f j).comp (F.map a).hom.toLinearMap = f i) :
    ∃! g : (colimit F : CommAlgCat.{v} R) →ₗ[R] P,
      ∀ i : I, g.comp (colimit.ι F i).hom.toLinearMap = f i := by
  sorry

end CommAlgCat
