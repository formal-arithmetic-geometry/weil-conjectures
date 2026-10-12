/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Sheaf.CategoryTheory.SiteFilteredColimitSections
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Degree-zero representatives on a fixed site

Source: Stacks Project, Tags 0738 and 03CO; degree zero in Tag 09YP.
(blueprint: lem-weil-pbc-fixed-site-degree-zero-representatives).
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private noncomputable def degreeZeroEquiv
    {C : Type u} [SmallCategory C] (T : GrothendieckTopology C)
    [HasSheafify T AddCommGrpCat.{u}] [HasExt.{u} (Sheaf T AddCommGrpCat.{u})]
    (A : Sheaf T AddCommGrpCat.{u}) (X : C) :
    Sheaf.H' A 0 X ≃ A.obj.obj (op X) :=
  Abelian.Ext.homEquiv₀ |>.trans
    ((sheafificationAdjunction T AddCommGrpCat.{u}).homEquiv _ A) |>.trans
    ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ A.obj) |>.trans yonedaEquiv

set_option backward.isDefEq.respectTransparency false in
private lemma degreeZeroEquiv_naturality
    {C : Type u} [SmallCategory C] (T : GrothendieckTopology C)
    [HasSheafify T AddCommGrpCat.{u}] [HasExt.{u} (Sheaf T AddCommGrpCat.{u})]
    {A B : Sheaf T AddCommGrpCat.{u}} (f : A ⟶ B) (X : C) (x : Sheaf.H' A 0 X) :
    degreeZeroEquiv T B X
        ((((Sheaf.cohomologyPresheafFunctor T 0).map f).app (op X)).hom x) =
      (f.hom.app (op X)).hom (degreeZeroEquiv T A X x) := by
  have h : Abelian.Ext.homEquiv₀
      ((((Sheaf.cohomologyPresheafFunctor T 0).map f).app (op X)).hom x) =
      Abelian.Ext.homEquiv₀ x ≫ f := by
    apply Abelian.Ext.homEquiv₀.symm.injective
    simp only [Equiv.symm_apply_apply, Abelian.Ext.homEquiv₀_symm_apply]
    change x.comp (Abelian.Ext.mk₀ f) (add_zero 0) =
      Abelian.Ext.mk₀ (Abelian.Ext.homEquiv₀ x ≫ f)
    rw [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_homEquiv₀_apply]
  simp only [degreeZeroEquiv, Equiv.trans_apply]
  erw [h]
  erw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right]
  rfl

/-- Degree-zero classes on a filtered colimit of sheaves on one finite-covering site
come from a member of the diagram.

Source: Stacks Project, Sites, Tag 0738(4), and Modules on Sites, Tag 03CO;
Cohomology on Sites, degree zero in Tag 09YP.
(blueprint: lem-weil-pbc-fixed-site-degree-zero-representatives).

Proof: identify Ext-zero from the free abelian sheaf on X with A(X), by the Ext-zero
bijection, the sheafification adjunction, the free-forgetful adjunction and Yoneda.
This identification is natural in A. The finite-covering section comparison is an
isomorphism. Lift the corresponding section through it, choose a representative in
the filtered colimit of groups, and use naturality and injectivity of the
identification to obtain the claimed equality in degree-zero cohomology.
-/
theorem finiteCover_degreeZero_colimit_representatives
    {C : Type u} [SmallCategory C] (P : Precoverage C)
    [P.HasIsos] [P.IsStableUnderComposition] [P.IsStableUnderBaseChange] [P.HasPullbacks]
    (hfinite : P ≤ Precoverage.finite C)
    [HasSheafify P.toGrothendieck AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf P.toGrothendieck AddCommGrpCat.{u})]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (S : J ⥤ Sheaf P.toGrothendieck AddCommGrpCat.{u})
    (K : Cocone S) (hK : IsColimit K) (X : C) (y : Sheaf.H' K.pt 0 X) :
    ∃ (j : J) (z : Sheaf.H' (S.obj j) 0 X),
      ((((Sheaf.cohomologyPresheafFunctor P.toGrothendieck 0).map
        (K.ι.app j)).app (op X)).hom z) = y := by
  let E := (sheafSections P.toGrothendieck AddCommGrpCat.{u}).obj (op X)
  let L := colimit.desc (S ⋙ E) (E.mapCocone K)
  have : IsIso L := siteFilteredColimit_sections_isIso P hfinite S K hK X
  obtain ⟨w, hw⟩ := (ConcreteCategory.bijective_of_isIso L).2
    (degreeZeroEquiv P.toGrothendieck K.pt X y)
  obtain ⟨j, z, rfl⟩ := Concrete.colimit_exists_rep (S ⋙ E) w
  refine ⟨j, (degreeZeroEquiv P.toGrothendieck (S.obj j) X).symm z, ?_⟩
  apply (degreeZeroEquiv P.toGrothendieck K.pt X).injective
  erw [degreeZeroEquiv_naturality, Equiv.apply_symm_apply]
  change (colimit.ι (S ⋙ E) j ≫ L).hom z = _ at hw
  rw [show L = colimit.desc (S ⋙ E) (E.mapCocone K) from rfl,
    colimit.ι_desc] at hw
  exact hw

end CategoryTheory
