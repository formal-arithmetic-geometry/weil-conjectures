/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.CategoryTheory.SiteCechComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Comparing chosen-product and Mathlib Čech complexes

Source: Stacks Project, Cohomology on Sites, Tags 03AK and 03AM.
(blueprint: lem-weil-pbc-site-cech-mathlib-comparison)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SiteCechComplex

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- Any choice of the iterated fibre products gives the Mathlib Čech complex up to
isomorphism, for every abelian presheaf and every family of arrows.

Source: Stacks Project, Cohomology on Sites, Tags 03AK and 03AM; the universal-property
comparison in step 3 of lem-weil-pbc-injective-etale-module-cech-h1.
(blueprint: lem-weil-pbc-site-cech-mathlib-comparison)

Proof: For each tuple t, the underlying object of the categorical product of the
objects Over.mk (hom (t k)) is a fibre product over U. Its projections satisfy the
same universal property as S.W p t. The unique projection-compatible maps in both
directions are inverse, since both composites have the identity's projections.
Restriction along these isomorphisms identifies the section groups. The categorical
product of abelian groups is isomorphic to the group of tuples of sections, by its
projection universal property, so these identifications give an isomorphism in each
degree. For every index injection omitting one factor, both composites of the product
comparison and the corresponding index maps have the same projections, hence agree.
Functoriality of restriction shows that the degree isomorphisms commute with every
term of the alternating sum, and therefore with the differential. Their inverses
also commute, yielding an isomorphism of cochain complexes. Empty families cause no
exception: the products of section groups over the empty tuple-index set are zero
objects in every degree. No sheaf, covering or injectivity hypothesis is used. -/
theorem mathlib_complex_iso_exists
    {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C]
    {U : C} {I : Type w} (V : I → C) (f : ∀ i, V i ⟶ U)
    (S : SiteCechComplex V f) (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    Nonempty (S.complex F ≅
      (cechComplexFunctor fun i : I ↦ Over.mk (f i)).obj ((Over.forget U).op ⋙ F)) :=
  by sorry

end CategoryTheory.SiteCechComplex
