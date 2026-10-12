/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-!
# Object cohomology as derived sections

Source: Stacks Project, Cohomology on Sites, Section 01FT.
(blueprint: lem-sc-site-cohomology-right-derived-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

/-- Ext cohomology over an object agrees naturally with the right derived sections functor.
Source: Stacks Project, Cohomology on Sites, Section 01FT; the convention in
`def-weil-pbc-sites-and-cohomology`.
(blueprint: lem-sc-site-cohomology-right-derived-sections).

Proof: the free abelian sheaf on the representable of `U` represents sections over `U`.
Indeed, sheafification adjunction, the free-abelian/forgetful adjunction, and Yoneda
identify morphisms from this sheaf to `F` with `F(U)`, naturally and additively in `F`.
Apply these identifications degreewise to an injective resolution of `F`. Ext from the
representing sheaf is the cohomology of its Hom complex, which is consequently the
complex of sections of the resolution. This computes the right derived sections.
Comparison maps lifting morphisms of sheaves commute with the degreewise identification;
homotopic comparison maps induce equal maps on cohomology. The resulting isomorphisms
are therefore natural in `F`, giving the displayed natural isomorphism in every degree.
No compactness or nonemptiness of `U` is required. -/
theorem nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (U : C) (q : ℕ) :
    Nonempty ((cohomologyPresheafFunctor J q ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) ≅
      (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q) := by
  sorry

end CategoryTheory.Sheaf
