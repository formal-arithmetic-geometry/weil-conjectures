/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF project
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Mates of squares through reflectors

Source: Stacks Project, Tag 07A7, remark-base-change, and the reflector Hom bijection;
the abstract completion-unit calculation is agent supplied.
(blueprint: lem-sbc-reflector-square-mate-factorization)
-/

@[expose] public section

universe uS uT uX uY vS vT vX vY

namespace CategoryTheory.ReflectorSquare

/-- The reflected left functor is restriction followed by the target reflector.
Source: Tag 07A7 and the reflector Hom bijection, abstract completion-unit calculation.
(blueprint: lem-sbc-reflector-square-mate-factorization) -/
def left {A : Type uS} {B : Type uT} [Category.{vS} A] [Category.{vT} B]
    (p : ObjectProperty A) (q : ObjectProperty B) [Reflective q.ι] (L : A ⥤ B) :
    p.FullSubcategory ⥤ q.FullSubcategory :=
  p.ι ⋙ L ⋙ reflector q.ι

/-- Restrict a right adjoint which preserves the full subcategories.
Source: Tag 07A7 and the reflector Hom bijection, abstract completion-unit calculation.
(blueprint: lem-sbc-reflector-square-mate-factorization) -/
def right {A : Type uS} {B : Type uT} [Category.{vS} A] [Category.{vT} B]
    (p : ObjectProperty A) (q : ObjectProperty B) (R : B ⥤ A)
    (hR : ∀ N : q.FullSubcategory, p (R.obj N.obj)) :
    q.FullSubcategory ⥤ p.FullSubcategory :=
  p.lift (q.ι ⋙ R) hR

/-- The comparison from the ordinary left functor to its reflection is the target unit.
Source: Tag 07A7 and the reflector Hom bijection, abstract completion-unit calculation.
(blueprint: lem-sbc-reflector-square-mate-factorization) -/
def unit {A : Type uS} {B : Type uT} [Category.{vS} A] [Category.{vT} B]
    (p : ObjectProperty A) (q : ObjectProperty B) [Reflective q.ι] (L : A ⥤ B) :
    p.ι ⋙ L ⟶ left p q L ⋙ q.ι :=
  Functor.whiskerLeft (p.ι ⋙ L) (reflectorAdjunction q.ι).unit

/-- The reflected mate factors the ambient mate through the completion units, naturally
and uniquely, and has the stated ordinary transpose.

Source: Stacks Project, Tag 07A7, remark-base-change, combined with the reflector Hom
bijection. The following abstract completion-unit calculation is agent supplied.
(blueprint: lem-sbc-reflector-square-mate-factorization)

Proof plan:
1. Put M = D_g K and delta = the reflected g-counit. The specified Hom formula sends
   delta to the identity, as does the ordinary g-counit. Injectivity of the ordinary
   Hom bijection gives k_g followed by delta = the ordinary g-counit.
2. By def-weil-pbc-adjunction-mate (Mathlib's mateEquiv), the reflected h-transpose of
   alpha is theta_c followed by P_e(delta).
3. The specified reflected Hom formula identifies the ordinary h-transpose of alpha
   with k_h followed by that reflected transpose. Precompose further with L_h(k_f).
4. Substitute the square compatibility hypothesis, replacing theta_c and the two
   units on its source by theta and the two units on its target.
5. Naturality of the target reflection unit at L_e(delta) moves P_e(delta) across k_e.
   Functoriality and step 1 give theta followed by L_e(epsilon_g) followed by k_e.
6. The ambient mate has transpose theta followed by L_e(epsilon_g). Naturality of the
   h-counit at k_e gives the same transpose after applying R_h(k_e). Injectivity of the
   ordinary h Hom bijection proves the factorization and the displayed transpose.
7. The target R_h(P_e K) belongs to the X full subcategory. Injectivity of precomposition
   with k_f into this target proves uniqueness, using the reflector Hom bijection.
8. Both mates and all unit comparisons are natural transformations, so the component
   factorizations assemble into the asserted equality of natural transformations.
No completion unit or mate is inverted. -/
theorem mate_factorization
    {AS : Type uS} {AT : Type uT} {AX : Type uX} {AY : Type uY}
    [Category.{vS} AS] [Category.{vT} AT] [Category.{vX} AX] [Category.{vY} AY]
    (s : ObjectProperty AS) (t : ObjectProperty AT)
    (x : ObjectProperty AX) (y : ObjectProperty AY)
    [Reflective s.ι] [Reflective t.ι] [Reflective x.ι] [Reflective y.ι]
    (Lf : AS ⥤ AX) (Rf : AX ⥤ AS) (af : Lf ⊣ Rf)
    (Lg : AS ⥤ AT) (Rg : AT ⥤ AS) (ag : Lg ⊣ Rg)
    (Lh : AX ⥤ AY) (Rh : AY ⥤ AX) (ah : Lh ⊣ Rh)
    (Le : AT ⥤ AY) (Re : AY ⥤ AT) (ae : Le ⊣ Re)
    (hf : ∀ N : x.FullSubcategory, s (Rf.obj N.obj))
    (hg : ∀ N : t.FullSubcategory, s (Rg.obj N.obj))
    (hh : ∀ N : y.FullSubcategory, x (Rh.obj N.obj))
    (he : ∀ N : y.FullSubcategory, t (Re.obj N.obj))
    (acf : left s x Lf ⊣ right s x Rf hf)
    (acg : left s t Lg ⊣ right s t Rg hg)
    (ach : left x y Lh ⊣ right x y Rh hh)
    (ace : left t y Le ⊣ right t y Re he)
    (hcf : ∀ (M : s.FullSubcategory) (N : x.FullSubcategory)
      (a : (left s x Lf).obj M ⟶ N),
      (acf.homEquiv M N a).hom = af.homEquiv M.obj N.obj ((unit s x Lf).app M ≫ a.hom))
    (hcg : ∀ (M : s.FullSubcategory) (N : t.FullSubcategory)
      (a : (left s t Lg).obj M ⟶ N),
      (acg.homEquiv M N a).hom = ag.homEquiv M.obj N.obj ((unit s t Lg).app M ≫ a.hom))
    (hch : ∀ (M : x.FullSubcategory) (N : y.FullSubcategory)
      (a : (left x y Lh).obj M ⟶ N),
      (ach.homEquiv M N a).hom = ah.homEquiv M.obj N.obj ((unit x y Lh).app M ≫ a.hom))
    (hce : ∀ (M : t.FullSubcategory) (N : y.FullSubcategory)
      (a : (left t y Le).obj M ⟶ N),
      (ace.homEquiv M N a).hom = ae.homEquiv M.obj N.obj ((unit t y Le).app M ≫ a.hom))
    (θ : Lf ⋙ Lh ≅ Lg ⋙ Le)
    (θc : left s x Lf ⋙ left x y Lh ≅ left s t Lg ⋙ left t y Le)
    (hθ : ∀ M : s.FullSubcategory,
      Lh.map ((unit s x Lf).app M) ≫ (unit x y Lh).app ((left s x Lf).obj M) ≫
        (θc.hom.app M).hom =
      θ.hom.app M.obj ≫ Le.map ((unit s t Lg).app M) ≫
        (unit t y Le).app ((left s t Lg).obj M)) :
    (Functor.whiskerLeft (right s t Rg hg) (unit s x Lf) ≫
        Functor.whiskerRight (mateEquiv acg ach θc.hom).natTrans x.ι =
      Functor.whiskerLeft t.ι (mateEquiv ag ah θ.hom).natTrans ≫
        Functor.whiskerRight (unit t y Le) Rh) ∧
    (∀ K : t.FullSubcategory,
      (∀ a : (left s x Lf).obj ((right s t Rg hg).obj K) ⟶
          (right x y Rh hh).obj ((left t y Le).obj K),
        (unit s x Lf).app ((right s t Rg hg).obj K) ≫ a.hom =
            (mateEquiv ag ah θ.hom).app K.obj ≫ Rh.map ((unit t y Le).app K) →
          a = (mateEquiv acg ach θc.hom).app K) ∧
      (ah.homEquiv (Lf.obj (Rg.obj K.obj)) ((left t y Le).obj K).obj).symm
          ((unit s x Lf).app ((right s t Rg hg).obj K) ≫
            ((mateEquiv acg ach θc.hom).app K).hom) =
        θ.hom.app (Rg.obj K.obj) ≫ Le.map (ag.counit.app K.obj) ≫ (unit t y Le).app K) := by
  sorry

end CategoryTheory.ReflectorSquare
