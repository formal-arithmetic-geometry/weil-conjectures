/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Mathlib.CategoryTheory.EssentialImage

/-! # Conjugacy of the scalar-counit pair across site comparisons

Source: Weil conjectures blueprint, smooth purity, reduction of exceptional pullback,
Charts paragraph (blueprint: lem-sp-site-scalar-counit-pair-conjugacy).
-/

@[expose] public section

universe vXA vYA vXB vYB vXA' vYA' vXB' vYB'
universe uXA uYA uXB uYB uXA' uYA' uXB' uYB'

namespace CategoryTheory

/-- The two evaluation composites are separately conjugate through the specified site
and coefficient comparisons. Equality of the original pair therefore implies equality
of the transported pair on every object of the comparison target.

Source: Weil conjectures blueprint, smooth purity, reduction of exceptional pullback,
Charts paragraph (blueprint: lem-sp-site-scalar-counit-pair-conjugacy).
The letters D, E, D', E' and Z in the node are expanded in the conclusion below.

Proof:
1. Fix L, put M = HA(L), s = rA(L), and u = deltaY(L). Use naturality of epsB'
   at u and the evaluation formula h_eval_B to rewrite D' followed by u as
   CYB(epsB) after cB inverse, FB'(rB after HB'(u) after a'), and q'.
   Associativity is supplied by def-nagata-category.
2. Substitute h_right at L into the parenthesized composite. Functoriality of FB'
   splits it into the images of TX'(s), deltaX(M), and CXB(a(L)).
3. Naturality of cB at a(L) moves CXB(a(L)) past cB inverse. Naturality of q'
   at s moves TX'(s) past q'. Neither step requires a or q' to be invertible.
4. Compose h_left at M with cB(TX(M)) inverse and TY'(cA(M) inverse).
   Substitution and functoriality of CYB combine the three images into CYB(D).
   The remaining factors are Z, giving the first identity independently of D = E.
5. Apply TY' to h_eval_A. Naturality of deltaY at epsA(L) moves TY'(CYA(epsA(L)))
   past deltaY(L). This gives Z followed by CYB(E), independently of the first identity.
6. If D = E for all L, the identities give equality after deltaY(L); cancel this
   isomorphism. Essential surjectivity of CYA supplies, for each K, an L and an
   isomorphism t : CYA(L) ≅ K.
7. Naturality of q', a', epsB' shows that D' commutes with t; naturality of epsA'
   shows the same for E'. The equality at CYA(L) then yields equality at K by
   cancelling the image of t under HA' followed by FA' followed by TY'.
-/
theorem site_scalar_counit_pair_conjugacy
    {XA : Type uXA} {YA : Type uYA} {XB : Type uXB} {YB : Type uYB}
    {XA' : Type uXA'} {YA' : Type uYA'} {XB' : Type uXB'} {YB' : Type uYB'}
    [Category.{vXA} XA] [Category.{vYA} YA] [Category.{vXB} XB] [Category.{vYB} YB]
    [Category.{vXA'} XA'] [Category.{vYA'} YA']
    [Category.{vXB'} XB'] [Category.{vYB'} YB']
    (FA : XA ⥤ YA) (HA : YA ⥤ XA) (FB : XB ⥤ YB) (HB : YB ⥤ XB)
    (FA' : XA' ⥤ YA') (HA' : YA' ⥤ XA') (FB' : XB' ⥤ YB') (HB' : YB' ⥤ XB')
    (epsA : HA ⋙ FA ⟶ 𝟭 YA) (epsB : HB ⋙ FB ⟶ 𝟭 YB)
    (epsA' : HA' ⋙ FA' ⟶ 𝟭 YA') (epsB' : HB' ⋙ FB' ⟶ 𝟭 YB')
    (CXA : XA ⥤ XA') (CYA : YA ⥤ YA') (CXB : XB ⥤ XB') (CYB : YB ⥤ YB')
    [CYA.EssSurj]
    (cA : FA ⋙ CYA ≅ CXA ⋙ FA') (cB : FB ⋙ CYB ≅ CXB ⋙ FB')
    (rA : CYA ⋙ HA' ≅ HA ⋙ CXA) (rB : CYB ⋙ HB' ≅ HB ⋙ CXB)
    (h_eval_A : ∀ L : YA, epsA'.app (CYA.obj L) =
      FA'.map (rA.hom.app L) ≫ cA.inv.app (HA.obj L) ≫ CYA.map (epsA.app L))
    (h_eval_B : ∀ L : YB, epsB'.app (CYB.obj L) =
      FB'.map (rB.hom.app L) ≫ cB.inv.app (HB.obj L) ≫ CYB.map (epsB.app L))
    (TX : XA ⥤ XB) (TY : YA ⥤ YB) (TX' : XA' ⥤ XB') (TY' : YA' ⥤ YB')
    (deltaX : CXA ⋙ TX' ≅ TX ⋙ CXB) (deltaY : CYA ⋙ TY' ≅ TY ⋙ CYB)
    (q : FA ⋙ TY ⟶ TX ⋙ FB) (q' : FA' ⋙ TY' ⟶ TX' ⋙ FB')
    (a : HA ⋙ TX ⟶ TY ⋙ HB) (a' : HA' ⋙ TX' ⟶ TY' ⋙ HB')
    (h_left : ∀ M : XA,
      TY'.map (cA.hom.app M) ≫ q'.app (CXA.obj M) ≫ FB'.map (deltaX.hom.app M) =
        deltaY.hom.app (FA.obj M) ≫ CYB.map (q.app M) ≫ cB.hom.app (TX.obj M))
    (h_right : ∀ L : YA,
      a'.app (CYA.obj L) ≫ HB'.map (deltaY.hom.app L) ≫ rB.hom.app (TY.obj L) =
        TX'.map (rA.hom.app L) ≫ deltaX.hom.app (HA.obj L) ≫ CXB.map (a.app L)) :
    (∀ L : YA,
      (q'.app (HA'.obj (CYA.obj L)) ≫ FB'.map (a'.app (CYA.obj L)) ≫
          epsB'.app (TY'.obj (CYA.obj L))) ≫ deltaY.hom.app L =
        (TY'.map (FA'.map (rA.hom.app L)) ≫ TY'.map (cA.inv.app (HA.obj L)) ≫
          deltaY.hom.app (FA.obj (HA.obj L))) ≫
            CYB.map (q.app (HA.obj L) ≫ FB.map (a.app L) ≫ epsB.app (TY.obj L))) ∧
    (∀ L : YA,
      TY'.map (epsA'.app (CYA.obj L)) ≫ deltaY.hom.app L =
        (TY'.map (FA'.map (rA.hom.app L)) ≫ TY'.map (cA.inv.app (HA.obj L)) ≫
          deltaY.hom.app (FA.obj (HA.obj L))) ≫ CYB.map (TY.map (epsA.app L))) ∧
    ((∀ L : YA,
      q.app (HA.obj L) ≫ FB.map (a.app L) ≫ epsB.app (TY.obj L) = TY.map (epsA.app L)) →
      ∀ K : YA', q'.app (HA'.obj K) ≫ FB'.map (a'.app K) ≫ epsB'.app (TY'.obj K) =
        TY'.map (epsA'.app K)) := by
  have h_square (M : XA) :
      q'.app (CXA.obj M) ≫ FB'.map (deltaX.hom.app M) ≫ cB.inv.app (TX.obj M) =
        TY'.map (cA.inv.app M) ≫ deltaY.hom.app (FA.obj M) ≫ CYB.map (q.app M) := by
    have h := congrArg
      (fun f ↦ TY'.map (cA.inv.app M) ≫ f ≫ cB.inv.app (TX.obj M)) (h_left M)
    simpa [Category.assoc, ← Functor.map_comp_assoc] using h
  have hD (L : YA) :
      (q'.app (HA'.obj (CYA.obj L)) ≫ FB'.map (a'.app (CYA.obj L)) ≫
          epsB'.app (TY'.obj (CYA.obj L))) ≫ deltaY.hom.app L =
        (TY'.map (FA'.map (rA.hom.app L)) ≫ TY'.map (cA.inv.app (HA.obj L)) ≫
          deltaY.hom.app (FA.obj (HA.obj L))) ≫
            CYB.map (q.app (HA.obj L) ≫ FB.map (a.app L) ≫ epsB.app (TY.obj L)) := by
    have hn : FB'.map (HB'.map (deltaY.hom.app L)) ≫
        epsB'.app (CYB.obj (TY.obj L)) =
        epsB'.app (TY'.obj (CYA.obj L)) ≫ deltaY.hom.app L :=
      epsB'.naturality (deltaY.hom.app L)
    simp only [Category.assoc]
    rw [← hn, h_eval_B]
    rw [← FB'.map_comp_assoc, ← FB'.map_comp_assoc, Category.assoc, h_right]
    simp only [Functor.map_comp, Category.assoc]
    have hq := q'.naturality (rA.hom.app L)
    have hc := cB.inv.naturality (a.app L)
    dsimp only [Functor.comp_obj, Functor.comp_map] at hq hc
    rw [← reassoc_of% hq, reassoc_of% hc, reassoc_of% h_square (HA.obj L)]
  have hE (L : YA) :
      TY'.map (epsA'.app (CYA.obj L)) ≫ deltaY.hom.app L =
        (TY'.map (FA'.map (rA.hom.app L)) ≫ TY'.map (cA.inv.app (HA.obj L)) ≫
          deltaY.hom.app (FA.obj (HA.obj L))) ≫ CYB.map (TY.map (epsA.app L)) := by
    rw [h_eval_A]
    simp only [Functor.map_comp, Category.assoc]
    have hn : TY'.map (CYA.map (epsA.app L)) ≫ deltaY.hom.app L =
        deltaY.hom.app (FA.obj (HA.obj L)) ≫ CYB.map (TY.map (epsA.app L)) :=
      deltaY.hom.naturality (epsA.app L)
    rw [hn]
  refine ⟨hD, hE, ?_⟩
  intro h K
  have h_image (L : YA) :
      q'.app (HA'.obj (CYA.obj L)) ≫ FB'.map (a'.app (CYA.obj L)) ≫
          epsB'.app (TY'.obj (CYA.obj L)) = TY'.map (epsA'.app (CYA.obj L)) := by
    apply (cancel_mono (deltaY.hom.app L)).1
    rw [hD, hE, h L]
  obtain ⟨L, ⟨t⟩⟩ := Functor.EssSurj.mem_essImage CYA K
  apply (cancel_epi (TY'.map (FA'.map (HA'.map t.hom)))).1
  have hq : TY'.map (FA'.map (HA'.map t.hom)) ≫ q'.app (HA'.obj K) =
      q'.app (HA'.obj (CYA.obj L)) ≫ FB'.map (TX'.map (HA'.map t.hom)) :=
    q'.naturality (HA'.map t.hom)
  have ha : TX'.map (HA'.map t.hom) ≫ a'.app K =
      a'.app (CYA.obj L) ≫ HB'.map (TY'.map t.hom) := a'.naturality t.hom
  have hb : FB'.map (HB'.map (TY'.map t.hom)) ≫ epsB'.app (TY'.obj K) =
      epsB'.app (TY'.obj (CYA.obj L)) ≫ TY'.map t.hom :=
    epsB'.naturality (TY'.map t.hom)
  have he : FA'.map (HA'.map t.hom) ≫ epsA'.app K =
      epsA'.app (CYA.obj L) ≫ t.hom := epsA'.naturality t.hom
  calc
    _ = (q'.app (HA'.obj (CYA.obj L)) ≫ FB'.map (a'.app (CYA.obj L)) ≫
        epsB'.app (TY'.obj (CYA.obj L))) ≫ TY'.map t.hom := by
      rw [← Category.assoc, hq]
      simp only [Category.assoc]
      rw [← FB'.map_comp_assoc, ha]
      simp only [Functor.map_comp, Category.assoc]
      rw [hb]
    _ = TY'.map (epsA'.app (CYA.obj L)) ≫ TY'.map t.hom := by rw [h_image]
    _ = _ := by rw [← TY'.map_comp, ← he, TY'.map_comp]

end CategoryTheory
