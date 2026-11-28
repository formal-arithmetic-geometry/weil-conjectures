/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.Identity

/-!
# Trivialized pullbacks in an exchange formalism

In a `CategoryTheory.ExchangeFormalism`, let `t : X ⟶ X` be an endomorphism whose pullback is
trivialized, `τ : t^* ≅ 𝟭` (the motivating example is the absolute Frobenius of a scheme of
characteristic `p` acting on étale sheaves). The conjugate trivialization of the pushforward is
`ExchangeFormalism.pfTriv t τ : t_* ≅ 𝟭`.

If such trivializations `τ_X`, `τ_Y` of `t_X^*` and `t_Y^*` are compatible with the pullback along
`j : X ⟶ Y` with `t_X ≫ j = j ≫ t_Y`, in the sense that the two isomorphisms
`(t_X ≫ j)^* ≅ j^*` built from them agree, then

- the square isomorphism, the base change map and the exchange map of the square
  `t_X ≫ j = j ≫ t_Y` are the identity up to the trivializations (`sqIso_hom_of_triv`,
  `baseChange_of_triv`, `exchange_of_triv`);
- the composition isomorphisms of the pushforwards `(t_X ≫ j)_* ≅ t_X_* ⋙ j_*` and
  `(j ≫ t_Y)_* ≅ j_* ⋙ t_Y_*` agree up to the trivializations (`pfComp'_inv_of_triv`).
-/

@[expose] public section

universe w v₁ v u

namespace CategoryTheory.ExchangeFormalism

open TwoSquare

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞}
  (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪)

section Triv

variable {X Y : 𝒞}

/-- The trivialization `t_* ≅ 𝟭` of the pushforward along an endomorphism `t` whose pullback is
trivialized by `τ : t^* ≅ 𝟭`: the conjugate of `τ`. -/
def pfTriv (t : X ⟶ X) (τ : F.pb t ≅ 𝟭 (F.obj X)) : F.pf t ≅ 𝟭 (F.obj X) :=
  conjugateIsoEquiv (F.adj t) Adjunction.id τ.symm

lemma pfTriv_hom (t : X ⟶ X) (τ : F.pb t ≅ 𝟭 (F.obj X)) :
    (F.pfTriv t τ).hom = conjugateEquiv (F.adj t) Adjunction.id τ.inv :=
  rfl

lemma pfTriv_inv (t : X ⟶ X) (τ : F.pb t ≅ 𝟭 (F.obj X)) :
    (F.pfTriv t τ).inv = conjugateEquiv Adjunction.id (F.adj t) τ.hom :=
  rfl

variable (tX : X ⟶ X) (tY : Y ⟶ Y) (τX : F.pb tX ≅ 𝟭 (F.obj X)) (τY : F.pb tY ≅ 𝟭 (F.obj Y))

/-- The square isomorphism of the square `t_X ≫ j = j ≫ t_Y` is the identity, up to the
trivializations `τ_X`, `τ_Y`, when these are compatible with the pullback along `j`. -/
lemma sqIso_hom_of_triv (j : X ⟶ Y) (w : tX ≫ j = j ≫ tY) (d : X ⟶ Y) (w₁ : tX ≫ j = d)
    (w₂ : j ≫ tY = d)
    (hτ : (F.pbComp' tX j d w₁).hom ≫ Functor.whiskerLeft (F.pb j) τX.hom ≫
        (Functor.rightUnitor (F.pb j)).hom =
      (F.pbComp' j tY d w₂).hom ≫ Functor.whiskerRight τY.hom (F.pb j) ≫
        (Functor.leftUnitor (F.pb j)).hom) :
    (F.sqIso tX j j tY w).hom =
      Functor.whiskerLeft (F.pb j) τX.hom ≫ (Functor.rightUnitor _).hom ≫
        (Functor.leftUnitor _).inv ≫ Functor.whiskerRight τY.inv (F.pb j) := by
  rw [F.sqIso_eq _ _ _ _ w d w₁ w₂, Iso.trans_hom, Iso.symm_hom, Iso.inv_comp_eq]
  ext M
  have h := congr_app hτ M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
    Category.comp_id, Functor.comp_obj, Functor.id_obj] at h ⊢
  rw [reassoc_of% h]
  simp [← Functor.map_comp]

/-- The base change map of the square `t_X ≫ j = j ≫ t_Y` is the identity, up to the
trivializations `τ_X`, `τ_Y`, when these are compatible with the pullback along `j`. -/
lemma baseChange_of_triv (j : X ⟶ Y) [Fact (𝒪 j)] (w : tX ≫ j = j ≫ tY) (d : X ⟶ Y)
    (w₁ : tX ≫ j = d) (w₂ : j ≫ tY = d)
    (hτ : (F.pbComp' tX j d w₁).hom ≫ Functor.whiskerLeft (F.pb j) τX.hom ≫
        (Functor.rightUnitor (F.pb j)).hom =
      (F.pbComp' j tY d w₂).hom ≫ Functor.whiskerRight τY.hom (F.pb j) ≫
        (Functor.leftUnitor (F.pb j)).hom) :
    F.baseChange tX j j tY w =
      ((TwoSquare.mk (𝟭 _) (F.sh j) (F.sh j) (𝟭 _)
        ((Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv)).whiskerTop
          τX.hom).whiskerBottom τY.inv := by
  apply (mateEquiv (F.shAdj j) (F.shAdj j)).injective
  rw [mateEquiv_whiskerTop_whiskerBottom, mateEquiv_unitors]
  simp only [baseChange, Equiv.apply_symm_apply, F.sqIso_hom_of_triv tX tY τX τY j w d w₁ w₂ hτ]
  ext M
  simp

/-- **The exchange map of a trivialized square**: the exchange map
`t_X_* ⋙ j_! ⟶ j_! ⋙ t_Y_*` of the square `t_X ≫ j = j ≫ t_Y` is the identity, up to the
trivializations `F.pfTriv tX τX` and `F.pfTriv tY τY`, when `τ_X` and `τ_Y` are compatible with
the pullback along `j`. -/
lemma exchange_of_triv (j : X ⟶ Y) [Fact (𝒪 j)] (w : tX ≫ j = j ≫ tY) (d : X ⟶ Y)
    (w₁ : tX ≫ j = d) (w₂ : j ≫ tY = d)
    (hτ : (F.pbComp' tX j d w₁).hom ≫ Functor.whiskerLeft (F.pb j) τX.hom ≫
        (Functor.rightUnitor (F.pb j)).hom =
      (F.pbComp' j tY d w₂).hom ≫ Functor.whiskerRight τY.hom (F.pb j) ≫
        (Functor.leftUnitor (F.pb j)).hom)
    [IsIso (F.baseChange tX j j tY w)] :
    F.exchange tX j j tY w =
      ((TwoSquare.mk (𝟭 _) (F.sh j) (F.sh j) (𝟭 _)
        ((Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv)).whiskerTop
          (F.pfTriv tX τX).hom).whiskerBottom (F.pfTriv tY τY).inv := by
  have key : inv (F.baseChange tX j j tY w) =
      ((TwoSquare.mk (F.sh j) (𝟭 _) (𝟭 _) (F.sh j)
        ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv)).whiskerLeft
          τX.inv).whiskerRight τY.hom := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [F.baseChange_of_triv tX tY τX τY j w d w₁ w₂ hτ]
    ext M
    simp [← Functor.map_comp]
  rw [exchange, key, mateEquiv_conjugateEquiv_vcomp _ Adjunction.id,
    conjugateEquiv_mateEquiv_vcomp _ Adjunction.id, mateEquiv_id_id_unitors]
  rfl

/-- The component form of `CategoryTheory.ExchangeFormalism.exchange_of_triv`. -/
lemma exchange_of_triv_app (j : X ⟶ Y) [Fact (𝒪 j)] (w : tX ≫ j = j ≫ tY) (d : X ⟶ Y)
    (w₁ : tX ≫ j = d) (w₂ : j ≫ tY = d)
    (hτ : (F.pbComp' tX j d w₁).hom ≫ Functor.whiskerLeft (F.pb j) τX.hom ≫
        (Functor.rightUnitor (F.pb j)).hom =
      (F.pbComp' j tY d w₂).hom ≫ Functor.whiskerRight τY.hom (F.pb j) ≫
        (Functor.leftUnitor (F.pb j)).hom)
    [IsIso (F.baseChange tX j j tY w)] (K : F.obj X) :
    (F.exchange tX j j tY w).app K =
      (F.sh j).map ((F.pfTriv tX τX).hom.app K) ≫ (F.pfTriv tY τY).inv.app ((F.sh j).obj K) := by
  rw [F.exchange_of_triv tX tY τX τY j w d w₁ w₂ hτ]
  simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom]

/-- **The composition isomorphisms of the pushforwards along a trivialized square**: for
`p : X ⟶ Y` with `t_X ≫ p = p ≫ t_Y = d` and trivializations `τ_X`, `τ_Y` compatible with the
pullback along `p`, the maps `p_* ⟶ d_*` obtained from `(t_X ≫ p)_* ≅ t_X_* ⋙ p_*` and from
`(p ≫ t_Y)_* ≅ p_* ⋙ t_Y_*` through the trivializations `F.pfTriv` agree. -/
lemma pfComp'_inv_of_triv (p : X ⟶ Y) (d : X ⟶ Y) (w₁ : tX ≫ p = d) (w₂ : p ≫ tY = d)
    (hτ : (F.pbComp' tX p d w₁).hom ≫ Functor.whiskerLeft (F.pb p) τX.hom ≫
        (Functor.rightUnitor (F.pb p)).hom =
      (F.pbComp' p tY d w₂).hom ≫ Functor.whiskerRight τY.hom (F.pb p) ≫
        (Functor.leftUnitor (F.pb p)).hom) :
    (Functor.leftUnitor (F.pf p)).inv ≫ Functor.whiskerRight (F.pfTriv tX τX).inv (F.pf p) ≫
        (F.pfComp' tX p d w₁).inv =
      (Functor.rightUnitor (F.pf p)).inv ≫ Functor.whiskerLeft (F.pf p) (F.pfTriv tY τY).inv ≫
        (F.pfComp' p tY d w₂).inv := by
  rw [pfComp'_inv, pfComp'_inv, pfTriv_inv, pfTriv_inv,
    ← conjugateEquiv_rightUnitor_hom (F.adj p), ← conjugateEquiv_leftUnitor_hom (F.adj p),
    ← conjugateEquiv_whiskerLeft _ _ (F.adj p), ← conjugateEquiv_whiskerRight _ _ (F.adj p),
    conjugateEquiv_comp, conjugateEquiv_comp, conjugateEquiv_comp, conjugateEquiv_comp]
  simp only [Category.assoc]
  rw [hτ]

/-- The component form of `CategoryTheory.ExchangeFormalism.pfComp'_inv_of_triv`. -/
lemma pfComp'_inv_of_triv_app (p : X ⟶ Y) (d : X ⟶ Y) (w₁ : tX ≫ p = d) (w₂ : p ≫ tY = d)
    (hτ : (F.pbComp' tX p d w₁).hom ≫ Functor.whiskerLeft (F.pb p) τX.hom ≫
        (Functor.rightUnitor (F.pb p)).hom =
      (F.pbComp' p tY d w₂).hom ≫ Functor.whiskerRight τY.hom (F.pb p) ≫
        (Functor.leftUnitor (F.pb p)).hom) (M : F.obj X) :
    (F.pf p).map ((F.pfTriv tX τX).inv.app M) ≫ (F.pfComp' tX p d w₁).inv.app M =
      (F.pfTriv tY τY).inv.app ((F.pf p).obj M) ≫ (F.pfComp' p tY d w₂).inv.app M := by
  simpa using congr_app (F.pfComp'_inv_of_triv tX tY τX τY p d w₁ w₂ hτ) M

end Triv

end CategoryTheory.ExchangeFormalism
