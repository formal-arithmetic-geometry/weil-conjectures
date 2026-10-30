/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-! # Normalized adjunction comparisons across equivalences

Source: Stacks Project, Tags 0B65 and 0DV0; categorical extension used in the blueprint
`det-nagata-density-normalization-sheaves`, Steps 1–2.
(auxiliary; not a blueprint node)

The three statements give the unique normalized comparison, its compatibility with
adjoint compositors, and the comparison of actual inverse mates. Diagram equalities
are stated at every object, equivalently as equalities of natural transformations.

## Main statements

- `exists_equivalenceAdjunctionComparison`: existence, uniqueness, Hom, unit and counit.
- `equivalenceAdjunctionComparison_compositor`: preservation of adjoint compositors.
- `equivalenceAdjunctionComparison_inverseMate`: inverse-mate equality and invertibility.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe uA vA uB vB uC vC uD vD uAb vAb uBb vBb uCb vCb uDb vDb

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {Ab : Type uAb} [Category.{vAb} Ab] {Bb : Type uBb} [Category.{vBb} Bb]
  {Cb : Type uCb} [Category.{vCb} Cb] {Db : Type uDb} [Category.{vDb} Db]

/-- Clause (1): a right-adjoint comparison across specified equivalences determines
one left-adjoint comparison, normalized by its inverse mate, and identifies all Hom
transposes, the units, and the counits. Applying this statement to C, D, Cb, Db gives
exactly the primed assertion of clause (1).

Source: Stacks Project, Tag 0B65; blueprint normalization proof, Step 1.
(auxiliary; not a blueprint node)

Proof: (1) Apply `isIso_inverseMate_of_equivalences` to the inverse mate alpha of u.
Set j = alpha inverse. Injectivity of `mateEquiv` gives uniqueness from normalization.
(2) Apply `adjunctionMate_transpose` to u and any f to obtain the full Hom equation.
Take f to be the identity of J X for the unit equation. Take X = U Y and f the counit
at Y for the counit equation, using the triangle identity for its transpose.
Repeat the same argument for the primed adjunctions. These are Steps 1–2 of the node. -/
theorem exists_equivalenceAdjunctionComparison
    (EA : A ≌ Ab) (EB : B ≌ Bb)
    {J : A ⥤ B} {U : B ⥤ A} {Jb : Ab ⥤ Bb} {Ub : Bb ⥤ Ab}
    (adj : J ⊣ U) (adjb : Jb ⊣ Ub)
    (u : U ⋙ EA.functor ≅ EB.functor ⋙ Ub) :
    ∃ j : J ⋙ EB.functor ≅ EA.functor ⋙ Jb,
      (mateEquiv adj adjb j.inv).natTrans = u.hom ∧
      (∀ k : J ⋙ EB.functor ≅ EA.functor ⋙ Jb,
        (mateEquiv adj adjb k.inv).natTrans = u.hom → k = j) ∧
      (∀ (X : A) (Y : B) (f : J.obj X ⟶ Y),
        adjb.homEquiv (EA.functor.obj X) (EB.functor.obj Y)
            (j.inv.app X ≫ EB.functor.map f) =
          EA.functor.map (adj.homEquiv X Y f) ≫ u.hom.app Y) ∧
      (∀ X : A, adjb.unit.app (EA.functor.obj X) ≫ Ub.map (j.inv.app X) =
        EA.functor.map (adj.unit.app X) ≫ u.hom.app (J.obj X)) ∧
      (∀ Y : B, j.inv.app (U.obj Y) ≫ EB.functor.map (adj.counit.app Y) =
        Jb.map (u.hom.app Y) ≫ adjb.counit.app (EB.functor.obj Y)) := by
  let alpha := ((mateEquiv adj adjb).symm u.hom).natTrans
  let : IsIso alpha := isIso_inverseMate_of_equivalences adj adjb u
  let j : J ⋙ EB.functor ≅ EA.functor ⋙ Jb := (asIso alpha).symm
  have hj : (mateEquiv adj adjb j.inv).natTrans = u.hom := by
    exact congrArg TwoSquare.natTrans ((mateEquiv adj adjb).apply_symm_apply u.hom)
  refine ⟨j, hj, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have h : k.inv = j.inv := by
      apply (mateEquiv adj adjb).injective
      exact hk.trans hj.symm
    exact Iso.ext_inv h
  · intro X Y f
    exact adjunctionMate_transpose adj adjb u.hom X Y f
  · intro X
    exact (unit_mateEquiv_symm adj adjb u.hom X).symm
  · intro Y
    exact (mateEquiv_counit_symm adj adjb u.hom Y).symm

end CategoryTheory
