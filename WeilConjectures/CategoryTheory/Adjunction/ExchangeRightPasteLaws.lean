/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste

/-!
# Identity and pasting laws of exchange morphisms

* `CategoryTheory.mateEquiv_app_of_isoId`: the mate of a square whose horizontal functors are
  identified with identities;
* `CategoryTheory.Adjunction.exchangeRight_app_paste_of_eq`: the horizontal pasting law
  `CategoryTheory.Adjunction.exchangeRight_app_paste`, solved for the outer square;
* `CategoryTheory.Adjunction.exchangeRight_app_paste_vert`: the vertical pasting law.

The pasting laws are stated for natural transformations *equal* to exchange morphisms, so that
they apply to maps defined as exchange morphisms without unfolding them.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

/-- The mate of a transformation `θ : G ⋙ L ⟶ L ⋙ H` of the form `L(I₁) ≫ I₂⁻¹`, for isomorphisms
`I₁ : G ≅ 𝟭` and `I₂ : H ≅ 𝟭`, is `I₁(R) ≫ R(I₂⁻¹)`. -/
lemma mateEquiv_app_of_isoId {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {G : C ⥤ C} {H : D ⥤ D} (I₁ : G ≅ 𝟭 C) (I₂ : H ≅ 𝟭 D) (θ : G ⋙ L ⟶ L ⋙ H)
    (hθ : ∀ B, θ.app B = L.map (I₁.hom.app B) ≫ I₂.inv.app (L.obj B)) (Y : D) :
    (mateEquiv a a θ).app Y = I₁.hom.app (R.obj Y) ≫ R.map (I₂.inv.app Y) := by
  apply (a.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, mateEquiv_counit, hθ,
    Functor.map_comp, Category.assoc, Category.assoc, a.counit_naturality]
  have h := I₂.inv.naturality (a.counit.app Y)
  simp only [Functor.id_map, Functor.id_obj] at h
  rw [h]
  simp

end CategoryTheory

namespace CategoryTheory.Adjunction

/-! The statements below are about natural transformations `bc` *equal* to exchange morphisms,
so that they apply to base change maps defined as exchange morphisms without unfolding them. -/

section Horizontal

variable {A B A' B' A'' B'' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Category* A''] [Category* B''] {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}
  {Lf'' : B'' ⥤ A''} {Rf'' : A'' ⥤ B''}

/-- **Horizontal pasting law of exchange morphisms**, solved for the outer square: in the
situation of `CategoryTheory.Adjunction.exchangeRight_app_paste`, the exchange morphism `bc` of
the outer square is `c`, followed by the exchange morphisms `bc₁` and `bc₂` of the two squares
and by the inverse of `c'`. The squares are
```
B --G₁--> B' --G₂--> B''
|Lf        |Lf'       |Lf''
v          v           v
A --G₁'-> A' --G₂'-> A''
```
with right adjoints `Rf`, `Rf'`, `Rf''` going up, and `G ≅ G₁ ⋙ G₂`, `G' ≅ G₁' ⋙ G₂'`. -/
lemma exchangeRight_app_paste_of_eq {G₁ : B ⥤ B'} {G₁' : A ⥤ A'} {G₂ : B' ⥤ B''}
    {G₂' : A' ⥤ A''} {G : B ⥤ B''} {G' : A ⥤ A''} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf')
    (af'' : Lf'' ⊣ Rf'') (θ₁ : G₁ ⋙ Lf' ≅ Lf ⋙ G₁') (θ₂ : G₂ ⋙ Lf'' ≅ Lf' ⋙ G₂')
    (θ : G ⋙ Lf'' ≅ Lf ⋙ G') (c : G ≅ G₁ ⋙ G₂) (c' : G' ≅ G₁' ⋙ G₂')
    (h : ∀ N : B, Lf''.map (c.hom.app N) ≫ θ₂.hom.app (G₁.obj N) ≫ G₂'.map (θ₁.hom.app N) =
      θ.hom.app N ≫ c'.hom.app (Lf.obj N))
    (bc₁ : Rf ⋙ G₁ ⟶ G₁' ⋙ Rf') (bc₂ : Rf' ⋙ G₂ ⟶ G₂' ⋙ Rf'') (bc : Rf ⋙ G ⟶ G' ⋙ Rf'')
    (h₁ : bc₁ = exchangeRight af af' θ₁) (h₂ : bc₂ = exchangeRight af' af'' θ₂)
    (h₃ : bc = exchangeRight af af'' θ) (K : A) :
    c.hom.app (Rf.obj K) ≫ G₂.map (bc₁.app K) ≫ bc₂.app (G₁'.obj K) ≫
        Rf''.map (c'.inv.app K) = bc.app K := by
  subst h₁ h₂ h₃
  rw [reassoc_of% (exchangeRight_app_paste af af' af'' θ₁ θ₂ θ c c' h K), ← Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]

end Horizontal

section Vertical

/-- The diagram chase turning the pasting law of the transposed squares into the one used in
`CategoryTheory.Adjunction.exchangeRight_app_paste_vert`. -/
private lemma paste_vert_aux {C : Type*} [Category* C] {A B B' D E : C} (t : A ⟶ B)
    (t' : B ⟶ A) (ht : t ≫ t' = 𝟙 A) (x : B ⟶ B') (s : D ⟶ B') (s' : B' ⟶ D)
    (hs : s' ≫ s = 𝟙 B') (p : E ⟶ D) (p' : D ⟶ E) (hp : p' ≫ p = 𝟙 D) (y : A ⟶ E)
    (e : x ≫ s' ≫ p' = t' ≫ y) : t ≫ x = y ≫ p ≫ s := by
  have hy : y = t ≫ x ≫ s' ≫ p' := by rw [e, reassoc_of% ht]
  rw [hy]
  simp [reassoc_of% hp, hs]

variable {CX CY CZ CX' CY' CZ' : Type*} [Category* CX] [Category* CY] [Category* CZ]
  [Category* CX'] [Category* CY'] [Category* CZ']
  {Lf : CY ⥤ CX} {Rf : CX ⥤ CY} {Lg : CZ ⥤ CY} {Rg : CY ⥤ CZ} {Lfg : CZ ⥤ CX} {Rfg : CX ⥤ CZ}
  {Lf' : CY' ⥤ CX'} {Rf' : CX' ⥤ CY'} {Lg' : CZ' ⥤ CY'} {Rg' : CY' ⥤ CZ'}
  {Lfg' : CZ' ⥤ CX'} {Rfg' : CX' ⥤ CZ'} {Gx : CX ⥤ CX'} {Gy : CY ⥤ CY'} {Gz : CZ ⥤ CZ'}

/-- **Vertical pasting law of exchange morphisms.** Consider two vertically adjacent squares of
left adjoints
```
CZ --Gz--> CZ'
|Lg         |Lg'
v           v
CY --Gy--> CY'
|Lf         |Lf'
v           v
CX --Gx--> CX'
```
with comparisons `θ₁ : Gz ⋙ Lg' ≅ Lg ⋙ Gy` and `θ₂ : Gy ⋙ Lf' ≅ Lf ⋙ Gx`, and a comparison
`θ : Gz ⋙ Lfg' ≅ Lfg ⋙ Gx` of the outer square, compatible with them through isomorphisms
`c : Lfg ≅ Lg ⋙ Lf` and `c' : Lfg' ≅ Lg' ⋙ Lf'` (the compatibility `hc` is stated for the
inverse comparisons `θ₁f`, `θ₂f`, `θf`, those of the transposed squares). Let
`d : Rf ⋙ Rg ≅ Rfg` and `d' : Rf' ⋙ Rg' ≅ Rfg'` be the conjugates of `c` and `c'`
(expressed by the counit identities `hd`, `hd'`). Then the exchange morphism `bc` of `θ` is the
exchange morphism `bc₁` of `θ₁` at `Rf K` followed by `Rg'` of the exchange morphism `bc₂` of `θ₂`
at `K`, through `d` and `d'`. -/
lemma exchangeRight_app_paste_vert (af : Lf ⊣ Rf) (ag : Lg ⊣ Rg) (afg : Lfg ⊣ Rfg)
    (af' : Lf' ⊣ Rf') (ag' : Lg' ⊣ Rg') (afg' : Lfg' ⊣ Rfg')
    (θ₁ : Gz ⋙ Lg' ≅ Lg ⋙ Gy) (θ₂ : Gy ⋙ Lf' ≅ Lf ⋙ Gx) (θ : Gz ⋙ Lfg' ≅ Lfg ⋙ Gx)
    (c : Lfg ≅ Lg ⋙ Lf) (c' : Lfg' ≅ Lg' ⋙ Lf') (d : Rf ⋙ Rg ≅ Rfg) (d' : Rf' ⋙ Rg' ≅ Rfg')
    (θ₁f : Lg ⋙ Gy ≅ Gz ⋙ Lg') (θ₂f : Lf ⋙ Gx ≅ Gy ⋙ Lf') (θf : Lfg ⋙ Gx ≅ Gz ⋙ Lfg')
    (hθ₁ : θ₁f = θ₁.symm) (hθ₂ : θ₂f = θ₂.symm) (hθ : θf = θ.symm)
    (hc : ∀ N : CZ, Gx.map (c.hom.app N) ≫ θ₂f.hom.app (Lg.obj N) ≫ Lf'.map (θ₁f.hom.app N) =
      θf.hom.app N ≫ c'.hom.app (Gz.obj N))
    (hd : ∀ K : CX, Lfg.map (d.hom.app K) ≫ afg.counit.app K =
      c.hom.app (Rg.obj (Rf.obj K)) ≫ Lf.map (ag.counit.app (Rf.obj K)) ≫ af.counit.app K)
    (hd' : ∀ K : CX', Lfg'.map (d'.hom.app K) ≫ afg'.counit.app K =
      c'.hom.app (Rg'.obj (Rf'.obj K)) ≫ Lf'.map (ag'.counit.app (Rf'.obj K)) ≫
        af'.counit.app K)
    (bc₁ : Rg ⋙ Gz ⟶ Gy ⋙ Rg') (bc₂ : Rf ⋙ Gy ⟶ Gx ⋙ Rf') (bc : Rfg ⋙ Gz ⟶ Gx ⋙ Rfg')
    (h₁ : bc₁ = exchangeRight ag ag' θ₁) (h₂ : bc₂ = exchangeRight af af' θ₂)
    (h₃ : bc = exchangeRight afg afg' θ) (K : CX) :
    Gz.map (d.inv.app K) ≫ bc₁.app (Rf.obj K) ≫ Rg'.map (bc₂.app K) ≫ d'.hom.app (Gx.obj K) =
      bc.app K := by
  subst h₁ h₂ h₃ hθ₁ hθ₂ hθ
  have hc' (N : CZ) : θ.hom.app N ≫ Gx.map (c.hom.app N) =
      c'.hom.app (Gz.obj N) ≫ Lf'.map (θ₁.hom.app N) ≫ θ₂.hom.app (Lg.obj N) :=
    paste_vert_aux (θ.hom.app N) (θ.inv.app N) (by simp) _ (θ₂.hom.app _) (θ₂.inv.app _) (by simp)
      (Lf'.map (θ₁.hom.app N)) (Lf'.map (θ₁.inv.app N)) (by simp [← Functor.map_comp]) _ (hc N)
  have e : Lfg'.map ((exchangeRight afg afg' θ).app K) ≫ afg'.counit.app (Gx.obj K) =
      θ.hom.app (Rfg.obj K) ≫ Gx.map (afg.counit.app K) := by
    simp [exchangeRight_app]
  have e₁ : Lg'.map ((exchangeRight ag ag' θ₁).app (Rf.obj K)) ≫
      ag'.counit.app (Gy.obj (Rf.obj K)) =
      θ₁.hom.app (Rg.obj (Rf.obj K)) ≫ Gy.map (ag.counit.app (Rf.obj K)) := by
    simp [exchangeRight_app]
  have e₂ : Lf'.map ((exchangeRight af af' θ₂).app K) ≫ af'.counit.app (Gx.obj K) =
      θ₂.hom.app (Rf.obj K) ≫ Gx.map (af.counit.app K) := by
    simp [exchangeRight_app]
  apply (afg'.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [hd', e]
  have n₁ := c'.hom.naturality (Gz.map (d.inv.app K) ≫ (exchangeRight ag ag' θ₁).app (Rf.obj K) ≫
    Rg'.map ((exchangeRight af af' θ₂).app K))
  have n₂ := ag'.counit.naturality ((exchangeRight af af' θ₂).app K)
  have n₃ := θ₂.hom.naturality (ag.counit.app (Rf.obj K))
  have n₄ := θ.hom.naturality (d.inv.app K)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map,
    Functor.map_comp, Category.assoc] at n₁ n₂ n₃ n₄
  have n₅ := c'.hom.naturality (Gz.map (d.inv.app K))
  simp only [Functor.comp_obj, Functor.comp_map] at n₅
  have hε : afg.counit.app K = Lfg.map (d.inv.app K) ≫ c.hom.app (Rg.obj (Rf.obj K)) ≫
      Lf.map (ag.counit.app (Rf.obj K)) ≫ af.counit.app K := by
    rw [← hd K, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  have e₁' := congrArg Lf'.map e₁
  have n₂' := congrArg Lf'.map n₂
  simp only [Functor.map_comp] at e₁' n₂'
  rw [reassoc_of% n₁, reassoc_of% n₂', e₂, reassoc_of% e₁', hε]
  simp only [Functor.map_comp]
  rw [← reassoc_of% n₄, reassoc_of% hc', reassoc_of% n₅, ← reassoc_of% n₃]

end Vertical

end CategoryTheory.Adjunction
