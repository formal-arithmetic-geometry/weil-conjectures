/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.Functor

/-! # Object cohomology as homology of the presheaf resolution

Source: Stacks Project, Cohomology on Sites, Section 01FT and Tag 03F3.
(blueprint: lem-weil-pbc-object-cohomology-presheaf-resolution)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

/-- Object cohomology is naturally the objectwise homology of any injective resolution.
Source: Stacks Project, Section 01FT, definition of cohomology over an object;
Tag 03F3, proof. The Ext formulation uses the free abelian representable adjunction.
(blueprint: lem-weil-pbc-object-cohomology-presheaf-resolution)

Proof: For U in C, let A(U) be the sheafification of the free abelian presheaf
on yoneda(U). Sheafification, the free abelian adjunction and Yoneda give the
additive identification Hom(A(U),G) = G(U), natural in both U and G. Applied
degreewise to I, it identifies the Hom complex from A(U) with I evaluated at U.
Since I is an injective resolution, Ext(A(U),F,q) is the degree-q homology of
this complex. One can use the extended integer complex and then its nonnegative
restriction; q is nonnegative, and the negative terms are zero, including the
incoming differential for q=0. The identification is natural for morphisms U -> V:
precomposition with A(U) -> A(V) corresponds to the restriction G(V) -> G(U)
in every degree. Taking homology preserves this equality. The objectwise homology
in the presheaf category evaluates to these groups by exactness of evaluation.
Compute Ext using I in the sheaf morphism universe, compare the given HasExt
universe by the canonical universe-independent Ext equivalence, and lift both
group-valued presheaves to max(u,v,w). These component isomorphisms and the
restriction compatibility assemble into the displayed natural isomorphism.
No enough-injectives assumption is required since I is supplied. The assertion
includes the empty site, zero sheaf and degree zero. -/
theorem objectCohomologyPresheaf_resolution
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (I : InjectiveResolution F) (q : ℕ) :
    Nonempty
      (Sheaf.cohomologyPresheaf F q ⋙ AddCommGrpCat.uliftFunctor.{max u v, w} ≅
        (((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex (.up ℕ)).obj
          I.cocomplex).homology q ⋙ AddCommGrpCat.uliftFunctor.{max u w, v}) := by sorry
