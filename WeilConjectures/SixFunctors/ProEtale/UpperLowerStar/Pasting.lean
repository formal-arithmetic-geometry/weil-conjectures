/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence

/-!
# Pasting of the commutative square isomorphisms of pro-étale pullbacks

For a commutative square `a ≫ b = c ≫ d` of schemes, `ProEtale.upperStarCompIso` identifies
`b^* ⋙ a^*` with `d^* ⋙ c^*`. These isomorphisms paste horizontally and vertically, as
consequences of the associativity law `ProEtale.upperStarComp_assoc`.

## Main results

- `AlgebraicGeometry.ProEtale.upperStarComp_assoc_app`: the associativity law in components,
  with arbitrary composites.
- `AlgebraicGeometry.ProEtale.upperStarCompIso_hcomp_app` and
  `AlgebraicGeometry.ProEtale.upperStarCompIso_vcomp_app`: horizontal and vertical pasting.
-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]


lemma upperStarCongr_rfl' {Z W : Scheme.{u}} (g : Z ⟶ W) :
    upperStarCongr A (rfl : g = g) = Iso.refl _ :=
  rfl



/-- The associativity law for `ProEtale.upperStarComp` in components, with the composites given
up to equality. -/
lemma upperStarComp_assoc'_app {X Y Z V : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (gh : Y ⟶ V) (hgh : gh = g ≫ h) (fgh : X ⟶ V)
    (hfgh : fgh = f ≫ gh) (hfgh' : fgh = fg ≫ h) (M : Sheaf (Scheme.ProEt.topology V) A) :
    (upperStarCongr A hfgh).hom.app M ≫ (upperStarComp A f gh).hom.app M ≫
        (f)^*[A].map ((upperStarCongr A hgh).hom.app M ≫ (upperStarComp A g h).hom.app M) =
      (upperStarCongr A hfgh').hom.app M ≫ (upperStarComp A fg h).hom.app M ≫
        (upperStarCongr A hfg).hom.app ((h)^*[A].obj M) ≫
          (upperStarComp A f g).hom.app ((h)^*[A].obj M) := by
  subst hfg hgh hfgh
  have := congr_app (congrArg Iso.hom (upperStarComp_assoc A f g h)) M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom] at this
  rw [upperStarCongr_rfl' A (f ≫ g ≫ h), upperStarCongr_rfl' A (g ≫ h),
    upperStarCongr_rfl' A (f ≫ g)]
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rw [this]
  erw [Category.id_comp, Category.id_comp]

/-- **Horizontal pasting** of the square isomorphisms of pullbacks, with all composites given up
to equality: for squares `a₁ ≫ v₂ = d₁ = v₁ ≫ b₁` and `a₂ ≫ v₃ = d₂ = v₂ ≫ b₂`, the square
isomorphism of the composite square `a₁₂ ≫ v₃ = t = v₁ ≫ b₁₂` is obtained by pasting. -/
lemma upperStarComp_hpaste_app {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Scheme.{u}} (a₁ : X₁ ⟶ X₂) (a₂ : X₂ ⟶ X₃)
    (b₁ : Y₁ ⟶ Y₂) (b₂ : Y₂ ⟶ Y₃) (v₁ : X₁ ⟶ Y₁) (v₂ : X₂ ⟶ Y₂) (v₃ : X₃ ⟶ Y₃)
    (a₁₂ : X₁ ⟶ X₃) (ha : a₁₂ = a₁ ≫ a₂) (b₁₂ : Y₁ ⟶ Y₃) (hb : b₁₂ = b₁ ≫ b₂)
    (d₁ : X₁ ⟶ Y₂) (hd₁ : d₁ = a₁ ≫ v₂) (hd₁' : d₁ = v₁ ≫ b₁)
    (d₂ : X₂ ⟶ Y₃) (hd₂ : d₂ = a₂ ≫ v₃) (hd₂' : d₂ = v₂ ≫ b₂)
    (t : X₁ ⟶ Y₃) (ht : t = a₁₂ ≫ v₃) (ht' : t = v₁ ≫ b₁₂)
    (M : Sheaf (Scheme.ProEt.topology Y₃) A) :
    (upperStarCongr A ht).hom.app M ≫ (upperStarComp A a₁₂ v₃).hom.app M ≫
        (upperStarCongr A ha).hom.app ((v₃)^*[A].obj M) ≫
        (upperStarComp A a₁ a₂).hom.app ((v₃)^*[A].obj M) ≫
        (a₁)^*[A].map ((upperStarComp A a₂ v₃).inv.app M ≫ (upperStarCongr A hd₂).inv.app M ≫
          (upperStarCongr A hd₂').hom.app M ≫ (upperStarComp A v₂ b₂).hom.app M) ≫
        (upperStarComp A a₁ v₂).inv.app ((b₂)^*[A].obj M) ≫
        (upperStarCongr A hd₁).inv.app ((b₂)^*[A].obj M) ≫
        (upperStarCongr A hd₁').hom.app ((b₂)^*[A].obj M) ≫
        (upperStarComp A v₁ b₁).hom.app ((b₂)^*[A].obj M) =
      (upperStarCongr A ht').hom.app M ≫ (upperStarComp A v₁ b₁₂).hom.app M ≫
        (v₁)^*[A].map ((upperStarCongr A hb).hom.app M ≫ (upperStarComp A b₁ b₂).hom.app M) := by
  have hT : t = a₁ ≫ d₂ := by rw [ht, ha, hd₂, Category.assoc]
  have hT' : t = d₁ ≫ b₂ := by rw [ht, ha, hd₁, Category.assoc, ← hd₂, hd₂', Category.assoc]
  have E1 := upperStarComp_assoc'_app A a₁ a₂ v₃ a₁₂ ha d₂ hd₂ t hT ht M
  have E2 := upperStarComp_assoc'_app A a₁ v₂ b₂ d₁ hd₁ d₂ hd₂' t hT hT' M
  have E3 := upperStarComp_assoc'_app A v₁ b₁ b₂ d₁ hd₁' b₁₂ hb t ht' hT' M
  have E1' (Z : Sheaf (Scheme.ProEt.topology X₁) A)
      (k : ((a₂)^*[A] ⋙ (a₁)^*[A]).obj ((v₃)^*[A].obj M) ⟶ Z) :
      (upperStarCongr A ht).hom.app M ≫ (upperStarComp A a₁₂ v₃).hom.app M ≫
        (upperStarCongr A ha).hom.app ((v₃)^*[A].obj M) ≫
        (upperStarComp A a₁ a₂).hom.app ((v₃)^*[A].obj M) ≫ k =
      (upperStarCongr A hT).hom.app M ≫ (upperStarComp A a₁ d₂).hom.app M ≫
        (a₁)^*[A].map ((upperStarCongr A hd₂).hom.app M ≫ (upperStarComp A a₂ v₃).hom.app M) ≫
          k := by
    simpa only [Category.assoc] using (congrArg (· ≫ k) E1).symm
  have E2' (Z : Sheaf (Scheme.ProEt.topology X₁) A)
      (k : ((b₂)^*[A] ⋙ (v₂)^*[A] ⋙ (a₁)^*[A]).obj M ⟶ Z) :
      (upperStarCongr A hT).hom.app M ≫ (upperStarComp A a₁ d₂).hom.app M ≫
        (a₁)^*[A].map ((upperStarCongr A hd₂').hom.app M ≫ (upperStarComp A v₂ b₂).hom.app M) ≫
          k =
      (upperStarCongr A hT').hom.app M ≫ (upperStarComp A d₁ b₂).hom.app M ≫
        (upperStarCongr A hd₁).hom.app ((b₂)^*[A].obj M) ≫
        (upperStarComp A a₁ v₂).hom.app ((b₂)^*[A].obj M) ≫ k := by
    simpa only [Category.assoc] using congrArg (· ≫ k) E2
  rw [E3, E1', ← Functor.map_comp_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [E2']
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

/-- **Vertical pasting** of the square isomorphisms of pullbacks, with all composites given up to
equality: for squares `a ≫ t' = p = t ≫ e` and `e ≫ u' = q = u ≫ d`, the square isomorphism of
the composite square `a ≫ (t' ≫ u') = r = (t ≫ u) ≫ d` is obtained by pasting. -/
lemma upperStarComp_vpaste_app {W₁ W₂ X₁ X₂ Y₁ Y₂ : Scheme.{u}} (a : W₁ ⟶ W₂) (t' : W₂ ⟶ X₂)
    (t : W₁ ⟶ X₁) (e : X₁ ⟶ X₂) (u' : X₂ ⟶ Y₂) (u : X₁ ⟶ Y₁) (d : Y₁ ⟶ Y₂)
    (p : W₁ ⟶ X₂) (hp : p = a ≫ t') (hp' : p = t ≫ e)
    (q : X₁ ⟶ Y₂) (hq : q = e ≫ u') (hq' : q = u ≫ d)
    (tu : W₁ ⟶ Y₁) (htu : tu = t ≫ u) (tu' : W₂ ⟶ Y₂) (htu' : tu' = t' ≫ u')
    (r : W₁ ⟶ Y₂) (hr : r = a ≫ tu') (hr' : r = tu ≫ d)
    (M : Sheaf (Scheme.ProEt.topology Y₂) A) :
    (upperStarCongr A hr).hom.app M ≫ (upperStarComp A a tu').hom.app M ≫
        (a)^*[A].map ((upperStarCongr A htu').hom.app M ≫ (upperStarComp A t' u').hom.app M) ≫
        (upperStarComp A a t').inv.app ((u')^*[A].obj M) ≫
        (upperStarCongr A hp).inv.app ((u')^*[A].obj M) ≫
        (upperStarCongr A hp').hom.app ((u')^*[A].obj M) ≫
        (upperStarComp A t e).hom.app ((u')^*[A].obj M) ≫
        (t)^*[A].map ((upperStarComp A e u').inv.app M ≫ (upperStarCongr A hq).inv.app M ≫
          (upperStarCongr A hq').hom.app M ≫ (upperStarComp A u d).hom.app M) =
      (upperStarCongr A hr').hom.app M ≫ (upperStarComp A tu d).hom.app M ≫
        (upperStarCongr A htu).hom.app ((d)^*[A].obj M) ≫
        (upperStarComp A t u).hom.app ((d)^*[A].obj M) := by
  have hR : r = p ≫ u' := by rw [hr, htu', hp, Category.assoc]
  have hR₂ : r = t ≫ q := by rw [hR, hp', hq, Category.assoc]
  have F1 := upperStarComp_assoc'_app A a t' u' p hp tu' htu' r hr hR M
  have F2 := upperStarComp_assoc'_app A t e u' p hp' q hq r hR₂ hR M
  have F3 := upperStarComp_assoc'_app A t u d tu htu q hq' r hR₂ hr' M
  have F1' (Z : Sheaf (Scheme.ProEt.topology W₁) A)
      (k : ((t')^*[A] ⋙ (a)^*[A]).obj ((u')^*[A].obj M) ⟶ Z) :
      (upperStarCongr A hr).hom.app M ≫ (upperStarComp A a tu').hom.app M ≫
        (a)^*[A].map ((upperStarCongr A htu').hom.app M ≫ (upperStarComp A t' u').hom.app M) ≫
          k =
      (upperStarCongr A hR).hom.app M ≫ (upperStarComp A p u').hom.app M ≫
        (upperStarCongr A hp).hom.app ((u')^*[A].obj M) ≫
        (upperStarComp A a t').hom.app ((u')^*[A].obj M) ≫ k := by
    simpa only [Category.assoc] using congrArg (· ≫ k) F1
  have F2' (Z : Sheaf (Scheme.ProEt.topology W₁) A)
      (k : ((e)^*[A] ⋙ (t)^*[A]).obj ((u')^*[A].obj M) ⟶ Z) :
      (upperStarCongr A hR).hom.app M ≫ (upperStarComp A p u').hom.app M ≫
        (upperStarCongr A hp').hom.app ((u')^*[A].obj M) ≫
        (upperStarComp A t e).hom.app ((u')^*[A].obj M) ≫ k =
      (upperStarCongr A hR₂).hom.app M ≫ (upperStarComp A t q).hom.app M ≫
        (t)^*[A].map ((upperStarCongr A hq).hom.app M ≫ (upperStarComp A e u').hom.app M) ≫
          k := by
    simpa only [Category.assoc] using (congrArg (· ≫ k) F2).symm
  rw [F1', Iso.hom_inv_id_app_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [F2', ← Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  exact F3

end AlgebraicGeometry.ProEtale
