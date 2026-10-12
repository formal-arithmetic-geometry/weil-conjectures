/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Ext sheaf cohomology and right-derived evaluation

Source: Stacks Project, Cohomology on Sites, Section 21.2 (Definition of cohomology).
(blueprint: new-sheaf-cohomology-derived-evaluation)
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace CategoryTheory.Sheaf

/-- Ext from the constant integer sheaf computes right-derived evaluation at a
terminal object of the site, in positive degrees.
Source: Stacks Project, Cohomology on Sites, Section 21.2, definition of cohomology;
Mathlib's definition of Sheaf.H and computation of Ext by an injective resolution.
(blueprint: new-sheaf-cohomology-derived-evaluation)

Proof: Let Z be the constant sheaf associated to the lifted integers. The
constant-sheaf adjunction at the terminal object T, followed by evaluation at 1,
identifies Hom(Z,F) additively and naturally with F(T). Choose an injective
resolution of F. The same natural identification in every degree identifies its
Hom(Z,-) complex with its evaluation complex and commutes with differentials.
The cohomology of the first complex in degree q+1 is Ext^(q+1)(Z,F), by the
injective-resolution computation of Ext, hence is Sheaf.H F (q+1). The cohomology
of the second is the (q+1)-st right-derived evaluation of F, by the
injective-resolution computation of right-derived functors. Compose these additive
identifications. No injectivity
assumption on F is needed: its resolution is taken in the category of abelian sheaves. -/
theorem cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{w})]
    (T : C) (hT : Limits.IsTerminal T) (F : Sheaf J AddCommGrpCat.{w}) (q : ℕ) :
    Nonempty
      (Sheaf.H F (q + 1) ≃+
        (((sheafToPresheaf J AddCommGrpCat.{w} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (Opposite.op T)).rightDerived
            (q + 1)).obj F)) := by sorry

end CategoryTheory.Sheaf
