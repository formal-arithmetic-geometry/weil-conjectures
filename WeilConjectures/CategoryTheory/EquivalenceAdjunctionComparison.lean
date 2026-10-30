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

namespace CategoryTheory

section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {Ab : Type uAb} [Category.{vAb} Ab] {Bb : Type uBb} [Category.{vBb} Bb]
  {Cb : Type uCb} [Category.{vCb} Cb] {Db : Type uDb} [Category.{vDb} Db]

/-- Clause (2): normalized left comparisons preserve the specified adjoint compositors.
All equivalences, comparisons, and composite/direct adjunctions remain specified data.

Source: Stacks Project, Tags 0B65 and 0DV0; blueprint normalization proof, Step 1.
(blueprint: lem-sfb-equivalence-square-inverse-mate-coherence)

Proof: (3) Put alpha_ij = c_ij inverse. By `mateEquiv_hcomp`, their pasted left square
has mate the pasted right square, under `Adjunction.comp` on both sides. Apply
`conjugateEquiv_mateEquiv_vcomp` to the unbarred compositor and
`mateEquiv_conjugateEquiv_vcomp` to the barred compositor. Their prescribed conjugates
are delta inverse and deltab inverse. Thus the two left routes have mates given by
the corresponding right routes with these inverse compositors inserted.
(4) Cancel delta and deltab in hdelta to identify those mates. Injectivity of
`mateEquiv` identifies the left routes. Cancel the invertible alpha comparisons to
obtain the displayed equation. These are Steps 3–4 of the node. -/
theorem equivalenceAdjunctionComparison_compositor
    (E0 : A ≌ Ab) (E1 : B ≌ Bb) (E2 : C ≌ Cb)
    {L01 : A ⥤ B} {R10 : B ⥤ A} {L12 : B ⥤ C} {R21 : C ⥤ B}
    {L02 : A ⥤ C} {R20 : C ⥤ A}
    {Lb01 : Ab ⥤ Bb} {Rb10 : Bb ⥤ Ab} {Lb12 : Bb ⥤ Cb} {Rb21 : Cb ⥤ Bb}
    {Lb02 : Ab ⥤ Cb} {Rb20 : Cb ⥤ Ab}
    (adj01 : L01 ⊣ R10) (adj12 : L12 ⊣ R21) (adj02 : L02 ⊣ R20)
    (adjb01 : Lb01 ⊣ Rb10) (adjb12 : Lb12 ⊣ Rb21) (adjb02 : Lb02 ⊣ Rb20)
    (r01 : R10 ⋙ E0.functor ≅ E1.functor ⋙ Rb10)
    (r12 : R21 ⋙ E1.functor ≅ E2.functor ⋙ Rb21)
    (r02 : R20 ⋙ E0.functor ≅ E2.functor ⋙ Rb20)
    (c01 : L01 ⋙ E1.functor ≅ E0.functor ⋙ Lb01)
    (c12 : L12 ⋙ E2.functor ≅ E1.functor ⋙ Lb12)
    (c02 : L02 ⋙ E2.functor ≅ E0.functor ⋙ Lb02)
    (h01 : (mateEquiv adj01 adjb01 c01.inv).natTrans = r01.hom)
    (h12 : (mateEquiv adj12 adjb12 c12.inv).natTrans = r12.hom)
    (h02 : (mateEquiv adj02 adjb02 c02.inv).natTrans = r02.hom)
    (delta : R21 ⋙ R10 ≅ R20) (deltab : Rb21 ⋙ Rb10 ≅ Rb20)
    (hdelta : ∀ Z : C,
      r01.hom.app (R21.obj Z) ≫ Rb10.map (r12.hom.app Z) ≫
          deltab.hom.app (E2.functor.obj Z) =
        E0.functor.map (delta.hom.app Z) ≫ r02.hom.app Z)
    (a : L01 ⋙ L12 ≅ L02) (ab : Lb01 ⋙ Lb12 ≅ Lb02)
    (ha : conjugateEquiv adj02 (adj01.comp adj12) a.hom = delta.inv)
    (hab : conjugateEquiv adjb02 (adjb01.comp adjb12) ab.hom = deltab.inv) :
    ∀ X : A, E2.functor.map (a.hom.app X) ≫ c02.hom.app X =
      c12.hom.app (L01.obj X) ≫ Lb12.map (c01.hom.app X) ≫
        ab.hom.app (E0.functor.obj X) := by
  let alpha : TwoSquare E0.functor (L01 ⋙ L12) (Lb01 ⋙ Lb12) E2.functor :=
    TwoSquare.vComp c01.inv c12.inv
  have hm : mateEquiv (adj01.comp adj12) (adjb01.comp adjb12) alpha =
      TwoSquare.hComp r12.hom r01.hom := by
    rw [mateEquiv_hcomp]
    change TwoSquare.hComp ((mateEquiv adj12 adjb12 c12.inv).natTrans)
      ((mateEquiv adj01 adjb01 c01.inv).natTrans) = _
    rw [h01, h12]
  have hl := conjugateEquiv_mateEquiv_vcomp adj02 (adj01.comp adj12)
    (adjb01.comp adjb12) a.hom alpha
  have hr := mateEquiv_conjugateEquiv_vcomp adj02 adjb02
    (adjb01.comp adjb12) c02.inv ab.hom
  rw [hm, ha] at hl
  change mateEquiv adj02 adjb02 c02.inv = r02.hom at h02
  rw [h02, hab] at hr
  have he : alpha.whiskerLeft a.hom = TwoSquare.whiskerRight c02.inv ab.hom := by
    apply (mateEquiv adj02 (adjb01.comp adjb12)).injective
    rw [hl, hr]
    ext Z
    dsimp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp]
    simp only [Category.id_comp, Category.comp_id]
    change E0.functor.map (delta.inv.app Z) ≫
        (r01.hom.app (R21.obj Z) ≫ Rb10.map (r12.hom.app Z)) =
      r02.hom.app Z ≫ deltab.inv.app (E2.functor.obj Z)
    apply (cancel_mono (deltab.hom.app (E2.functor.obj Z))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [hdelta Z, ← Category.assoc, ← E0.functor.map_comp]
    simp
  intro X
  have hx := congrArg (fun t ↦ t.natTrans.app X) he
  dsimp [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, alpha, TwoSquare.vComp] at hx
  simp only [Category.id_comp, Category.comp_id] at hx
  change (Lb12.map (c01.inv.app X) ≫ c12.inv.app (L01.obj X)) ≫
      E2.functor.map (a.hom.app X) =
    ab.hom.app (E0.functor.obj X) ≫ c02.inv.app X at hx
  apply (cancel_epi (Lb12.map (c01.inv.app X) ≫ c12.inv.app (L01.obj X))).1
  simp only [← Category.assoc, hx]
  simp [← Lb12.map_comp, Category.assoc]

end

end CategoryTheory
