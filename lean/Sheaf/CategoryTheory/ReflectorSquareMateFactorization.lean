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
  have _ := hcf
  have _ := hce
  have hδ (K : t.FullSubcategory) :
      (unit s t Lg).app ((right s t Rg hg).obj K) ≫ (acg.counit.app K).hom =
        ag.counit.app K.obj := by
    apply (ag.homEquiv (Rg.obj K.obj) K.obj).injective
    erw [← hcg ((right s t Rg hg).obj K) K (acg.counit.app K)]
    simp only [← Adjunction.homEquiv_symm_id, Equiv.apply_symm_apply,
      ObjectProperty.FullSubcategory.id_hom]
    rfl
  have htrans (K : t.FullSubcategory) :
      (ah.homEquiv (Lf.obj (Rg.obj K.obj)) ((left t y Le).obj K).obj).symm
          ((unit s x Lf).app ((right s t Rg hg).obj K) ≫
            ((mateEquiv acg ach θc.hom).app K).hom) =
        θ.hom.app (Rg.obj K.obj) ≫ Le.map (ag.counit.app K.obj) ≫
          (unit t y Le).app K := by
    let M := (right s t Rg hg).obj K
    let N := (left t y Le).obj K
    let α := (mateEquiv acg ach θc.hom).app K
    have hc : (ah.homEquiv ((left s x Lf).obj M).obj N.obj).symm α.hom =
        (unit x y Lh).app ((left s x Lf).obj M) ≫
          ((ach.homEquiv ((left s x Lf).obj M) N).symm α).hom := by
      apply (ah.homEquiv _ _).injective
      rw [Equiv.apply_symm_apply, ← hch, Equiv.apply_symm_apply]
    have hr : (ach.homEquiv ((left s x Lf).obj M) N).symm α =
        θc.hom.app M ≫ (left t y Le).map (acg.counit.app K) := by
      rw [Adjunction.homEquiv_counit]
      exact mateEquiv_counit acg ach θc.hom K
    rw [hr, ObjectProperty.FullSubcategory.comp_hom] at hc
    have hn : (unit t y Le).app ((left s t Lg).obj M) ≫
          ((left t y Le).map (acg.counit.app K)).hom =
        Le.map (acg.counit.app K).hom ≫ (unit t y Le).app K :=
      ((unit t y Le).naturality (acg.counit.app K)).symm
    rw [ah.homEquiv_naturality_left_symm]
    erw [hc]
    calc
      _ = (Lh.map ((unit s x Lf).app M) ≫
            (unit x y Lh).app ((left s x Lf).obj M) ≫ (θc.hom.app M).hom) ≫
            ((left t y Le).map (acg.counit.app K)).hom := by
        simp only [Category.assoc, M]
      _ = (θ.hom.app M.obj ≫ Le.map ((unit s t Lg).app M) ≫
            (unit t y Le).app ((left s t Lg).obj M)) ≫
            ((left t y Le).map (acg.counit.app K)).hom := by rw [hθ M]
      _ = θ.hom.app M.obj ≫ Le.map ((unit s t Lg).app M) ≫
            Le.map (acg.counit.app K).hom ≫ (unit t y Le).app K := by
        simp only [Category.assoc]
        rw [hn]
      _ = θ.hom.app M.obj ≫
            Le.map ((unit s t Lg).app M ≫ (acg.counit.app K).hom) ≫
            (unit t y Le).app K := by rw [Le.map_comp, Category.assoc]
      _ = _ := by
        rw [hδ K]
        rfl
  have hfac (K : t.FullSubcategory) :
      (unit s x Lf).app ((right s t Rg hg).obj K) ≫
          ((mateEquiv acg ach θc.hom).app K).hom =
        (mateEquiv ag ah θ.hom).app K.obj ≫ Rh.map ((unit t y Le).app K) := by
    apply (ah.homEquiv _ _).symm.injective
    erw [htrans K, ah.homEquiv_naturality_right_symm, Adjunction.homEquiv_counit,
      mateEquiv_counit]
    simp only [Category.assoc]
  constructor
  · apply NatTrans.ext
    funext K
    exact hfac K
  · intro K
    refine ⟨?_, htrans K⟩
    intro a ha
    apply ObjectProperty.hom_ext
    apply (unitCompPartialBijectiveAux (i := x.ι)
      (Lf.obj (Rg.obj K.obj)) ((right x y Rh hh).obj ((left t y Le).obj K))).symm.injective
    rw [unitCompPartialBijectiveAux_symm_apply, unitCompPartialBijectiveAux_symm_apply]
    exact ha.trans (hfac K).symm

end CategoryTheory.ReflectorSquare
