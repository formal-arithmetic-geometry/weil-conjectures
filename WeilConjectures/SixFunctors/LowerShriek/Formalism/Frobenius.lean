/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.Frobenius
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Canonical

/-!
# Trivialized pullbacks and the composition isomorphism of a compact support formalism

Let `F` be a compact support formalism satisfying proper base change, and let `t_X`, `t_Y`
be proper endomorphisms of schemes `X`, `Y` whose pullbacks are trivialized, `τ : t^* ≅ 𝟭`
(the motivating example is the absolute Frobenius acting on étale sheaves). The compactly
supported direct image along `t` is then trivialized as well,
`F.lowerShriekTriv t τ : F.lowerShriek t ≅ 𝟭`.

For `f : X ⟶ Y` with `t_X ≫ f = f ≫ t_Y`, suppose that the chosen compactification
`X ⟶[i] Z ⟶[g] Y` of `f` carries an endomorphism `t_Z` with cartesian square `t_X ≫ i = i ≫ t_Z`
and with `t_Z ≫ g = g ≫ t_Y`, and that the trivializations are compatible with the pullbacks
along `i` and `g`. Then the two isomorphisms `(t_X ≫ f)_! = (f ≫ t_Y)_! ≅ f_!` obtained from the
composition isomorphisms and the trivializations agree
(`AlgebraicGeometry.CompactSupportFormalism.lowerShriekCompIso_inv_triv`).

The proof computes both composition isomorphisms with explicit triangles of compactifications
(`AlgebraicGeometry.Compactification.Triangle.ofEndoLeft`,
`AlgebraicGeometry.Compactification.Triangle.ofEndoRight`), on which they reduce to the exchange
map of the square `t_X ≫ i = i ≫ t_Z` and to the composition isomorphisms of the pushforwards,
which are trivial up to the trivializations
(`CategoryTheory.ExchangeFormalism.exchange_of_triv`,
`CategoryTheory.ExchangeFormalism.pfComp'_inv_of_triv`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Compactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The compactification `X ⟶[c.i] c.Z ⟶[t ≫ c.g] Y` of a morphism `f' = c.i ≫ t ≫ c.g`, for a
compactification `c` of `f` and a proper endomorphism `t` of `c.Z`. -/
@[simps]
def withEndo (c : Compactification f) (t : c.Z ⟶ c.Z) [IsProper t] {f' : X ⟶ Y}
    (h : f' = c.i ≫ t ≫ c.g) : Compactification f' where
  Z := c.Z
  g := t ≫ c.g
  i := c.i
  comm := h
  isProper := have := c.isProper; inferInstance
  isOpenImmersion := c.isOpenImmersion

namespace Triangle

variable (c : Compactification f)

/-- The triangle of compactifications of `(t_X, f)` attached to a compactification `c` of `f` and
endomorphisms `t_X`, `t_Z` of `X`, `c.Z` with cartesian square `t_X ≫ c.i = c.i ≫ t_Z`: the
trivial compactification of `t_X`, the compactification `c` of `f` and the compactification
`(c.i, t_Z ≫ c.g)` of `t_X ≫ f`, with `q = c.i` and `p = t_Z`. -/
@[simps]
def ofEndoLeft (tX : X ⟶ X) [IsProper tX] (tZ : c.Z ⟶ c.Z) [IsProper tZ]
    (h : IsPullback tX c.i c.i tZ) : Triangle tX f where
  cf := ofIsProper tX
  cg := c
  cfg := c.withEndo tZ (by
    conv_lhs => rw [c.comm]
    rw [← Category.assoc, h.w, Category.assoc])
  q := c.i
  p := tZ
  i_q := Category.id_comp _
  p_g := rfl
  isPullback := h

/-- The triangle of compactifications of `(f, t_Y)` attached to a compactification `c` of `f` and
endomorphisms `t_Y`, `t_Z` of `Y`, `c.Z` with `t_Z ≫ c.g = c.g ≫ t_Y`: the compactification `c`
of `f`, the trivial compactification of `t_Y` and the compactification `(c.i, t_Z ≫ c.g)` of
`f ≫ t_Y`, with `q = 𝟙` and `p = c.g`. -/
@[simps]
def ofEndoRight (tY : Y ⟶ Y) [IsProper tY]
    (tZ : c.Z ⟶ c.Z) [IsProper tZ] (h : tZ ≫ c.g = c.g ≫ tY) : Triangle f tY where
  cf := c
  cg := ofIsProper tY
  cfg := c.withEndo tZ (by
    rw [h]
    conv_lhs => rw [c.comm]
    rw [Category.assoc])
  q := 𝟙 c.Z
  p := c.g
  i_q := Category.comp_id _
  p_g := h.symm
  isPullback := (IsPullback.of_vert_isIso ⟨by simp⟩ : IsPullback c.g (𝟙 c.Z) (𝟙 Y) c.g)

end Triangle

end Compactification

namespace CompactSupportFormalism

variable (F : CompactSupportFormalism.{w, v, u})

section Triv

variable {X : Scheme.{u}}

/-- The trivialization `(𝟙 X)_! ⋙ t_* ≅ 𝟭` of the compactly supported direct image along the
trivial compactification of a proper endomorphism `t` whose pullback is trivialized by `τ`. -/
noncomputable def shriekOfIsProperTriv (t : X ⟶ X) [IsProper t] (τ : F.pb t ≅ 𝟭 (F.obj X)) :
    F.shriek (Compactification.ofIsProper t) ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (F.shId X) (F.pf t) ≪≫ Functor.leftUnitor _ ≪≫ F.pfTriv t τ

lemma shriekOfIsProperTriv_inv_app (t : X ⟶ X) [IsProper t] (τ : F.pb t ≅ 𝟭 (F.obj X))
    (K : F.obj X) :
    (F.shriekOfIsProperTriv t τ).inv.app K =
      (F.pfTriv t τ).inv.app K ≫ (F.pf t).map ((F.shId X).inv.app K) := by
  simp [shriekOfIsProperTriv]

variable [F.HasProperExchange]

/-- The trivialization `F.lowerShriek t ≅ 𝟭` of the compactly supported direct image along a
proper endomorphism `t` whose pullback is trivialized by `τ`. -/
noncomputable def lowerShriekTriv (t : X ⟶ X) [IsProper t] (τ : F.pb t ≅ 𝟭 (F.obj X)) :
    F.lowerShriek t ≅ 𝟭 _ :=
  F.shriekIso _ (Compactification.ofIsProper t) ≪≫ F.shriekOfIsProperTriv t τ

end Triv

variable [F.HasProperExchange]

section Triangle

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (tX : X ⟶ X) (tY : Y ⟶ Y)
  (tZ : c.Z ⟶ c.Z) [IsProper tX] [IsProper tY] [IsProper tZ]
  (τX : F.pb tX ≅ 𝟭 (F.obj X)) (τY : F.pb tY ≅ 𝟭 (F.obj Y)) (τZ : F.pb tZ ≅ 𝟭 (F.obj c.Z))

/-- The composition isomorphism of the triangle `Compactification.Triangle.ofEndoLeft`, precomposed
with the trivialization of `(t_X)_!`, is computed by the trivialization of `(t_Z)_*`. -/
lemma map_shriekOfIsProperTriv_inv_app_comp_compIso_ofEndoLeft_hom_app
    (hX : IsPullback tX c.i c.i tZ)
    (hi : (F.pbComp' tX c.i (tX ≫ c.i) rfl).hom ≫ Functor.whiskerLeft (F.pb c.i) τX.hom ≫
        (Functor.rightUnitor (F.pb c.i)).hom =
      (F.pbComp' c.i tZ (tX ≫ c.i) hX.w.symm).hom ≫ Functor.whiskerRight τZ.hom (F.pb c.i) ≫
        (Functor.leftUnitor (F.pb c.i)).hom) (K : F.obj X) :
    (F.shriek c).map ((F.shriekOfIsProperTriv tX τX).inv.app K) ≫
        (F.compIso (Compactification.Triangle.ofEndoLeft c tX tZ hX)).hom.app K =
      (F.pf c.g).map ((F.pfTriv tZ τZ).inv.app ((F.sh c.i).obj K)) ≫
        (F.pfComp' tZ c.g (tZ ≫ c.g) rfl).inv.app ((F.sh c.i).obj K) := by
  have : IsIso (F.baseChange tX c.i c.i tZ hX.w) := HasBaseChange.isIso_baseChange (F := F) hX
  have hE := F.exchange_of_triv_app tX tZ τX τZ c.i hX.w (tX ≫ c.i) rfl hX.w.symm hi K
  have hN := (F.exchange tX c.i c.i tZ hX.w).naturality ((F.shId X).inv.app K)
  have hS := congr_app (F.shComp'_id_left c.i) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Category.comp_id, NatTrans.id_app, Functor.comp_obj, Functor.id_obj] at hS
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hN
  have hinv : (F.shComp' (𝟙 X) c.i c.i (Category.id_comp _)).inv.app K =
      (F.sh c.i).map ((F.shId X).hom.app K) := by
    rw [← cancel_epi ((F.shComp' (𝟙 X) c.i c.i (Category.id_comp _)).hom.app K),
      Iso.hom_inv_id_app]
    exact hS.symm
  have key : (F.sh c.i).map ((F.pfTriv tX τX).inv.app K ≫ (F.pf tX).map ((F.shId X).inv.app K)) ≫
      (F.exchange tX c.i c.i tZ hX.w).app ((F.sh (𝟙 X)).obj K) ≫
      (F.pf tZ).map ((F.shComp' (𝟙 X) c.i c.i (Category.id_comp _)).inv.app K) =
      (F.pfTriv tZ τZ).inv.app ((F.sh c.i).obj K) := by
    rw [Functor.map_comp, Category.assoc, reassoc_of% hN, hinv, ← Functor.map_comp,
      ← Functor.map_comp, Iso.inv_hom_id_app]
    simp only [Functor.id_obj, CategoryTheory.Functor.map_id, Category.comp_id]
    rw [hE, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    simp
  rw [compIso_hom_app, shriekOfIsProperTriv_inv_app]
  refine (Functor.map_comp_assoc (F.pf c.g) _ _ _).symm.trans ?_
  exact congrArg (fun x ↦ (F.pf c.g).map x ≫
    (F.pfComp' tZ c.g (tZ ≫ c.g) rfl).inv.app ((F.sh c.i).obj K)) key

/-- The composition isomorphism of the triangle `Compactification.Triangle.ofEndoRight`,
precomposed with the trivialization of `(t_Y)_!`, is the composition isomorphism of the
pushforwards along `c.g ≫ t_Y = t_Z ≫ c.g`, up to the trivialization of `(t_Y)_*`. -/
lemma shriekOfIsProperTriv_inv_app_comp_compIso_ofEndoRight_hom_app
    (hg : tZ ≫ c.g = c.g ≫ tY) (K : F.obj X) :
    (F.shriekOfIsProperTriv tY τY).inv.app ((F.shriek c).obj K) ≫
        (F.compIso (Compactification.Triangle.ofEndoRight c tY tZ hg)).hom.app K =
      (F.pfTriv tY τY).inv.app ((F.pf c.g).obj ((F.sh c.i).obj K)) ≫
        (F.pfComp' c.g tY (tZ ≫ c.g) hg.symm).inv.app ((F.sh c.i).obj K) := by
  have hw : c.g ≫ 𝟙 Y = 𝟙 c.Z ≫ c.g := by rw [Category.id_comp, Category.comp_id]
  have : IsIso (F.baseChange c.g (𝟙 c.Z) (𝟙 Y) c.g hw) :=
    HasBaseChange.isIso_baseChange (F := F) (IsPullback.of_vert_isIso ⟨hw⟩)
  have h₁ := congr_app (F.exchange_id_vert c.g hw) ((F.sh c.i).obj K)
  have h₂ := congr_app (F.shComp'_id_right c.i) K
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Category.comp_id, Functor.comp_obj, Functor.id_obj,
    NatTrans.id_app] at h₁ h₂
  have hSC : (F.shComp' c.i (𝟙 c.Z) c.i (Category.comp_id _)).inv.app K =
      (F.shId c.Z).hom.app ((F.sh c.i).obj K) := by
    rw [← cancel_epi ((F.shComp' c.i (𝟙 c.Z) c.i (Category.comp_id _)).hom.app K),
      Iso.hom_inv_id_app]
    exact h₂.symm
  have key : (F.shId Y).inv.app ((F.pf c.g).obj ((F.sh c.i).obj K)) ≫
      (F.exchange c.g (𝟙 c.Z) (𝟙 Y) c.g hw).app ((F.sh c.i).obj K) ≫
      (F.pf c.g).map ((F.shComp' c.i (𝟙 c.Z) c.i (Category.comp_id _)).inv.app K) = 𝟙 _ := by
    rw [h₁, hSC, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    simp
  rw [compIso_hom_app, shriekOfIsProperTriv_inv_app, Category.assoc]
  refine congrArg (fun x ↦ (F.pfTriv tY τY).inv.app ((F.pf c.g).obj ((F.sh c.i).obj K)) ≫ x) ?_
  refine (Functor.map_comp_assoc (F.pf tY) _ _ _).symm.trans ?_
  refine (congrArg (fun x ↦ (F.pf tY).map x ≫
    (F.pfComp' c.g tY (tZ ≫ c.g) hg.symm).inv.app ((F.sh c.i).obj K)) key).trans ?_
  simp

/-- **The composition isomorphisms of a trivialized square of compactifications**: the two maps
`(c.i, t_Z ≫ c.g)_! ⟶ c_!` obtained from the composition isomorphisms of the triangles
`Compactification.Triangle.ofEndoLeft` and `Compactification.Triangle.ofEndoRight` and the
trivializations of `(t_X)_!` and `(t_Y)_!` agree, if the trivializations `τ_X`, `τ_Y`, `τ_Z` are
compatible with the pullbacks along `c.i` and `c.g`. -/
theorem compIso_inv_ofEndo (hX : IsPullback tX c.i c.i tZ) (hg : tZ ≫ c.g = c.g ≫ tY)
    (hi : (F.pbComp' tX c.i (tX ≫ c.i) rfl).hom ≫ Functor.whiskerLeft (F.pb c.i) τX.hom ≫
        (Functor.rightUnitor (F.pb c.i)).hom =
      (F.pbComp' c.i tZ (tX ≫ c.i) hX.w.symm).hom ≫ Functor.whiskerRight τZ.hom (F.pb c.i) ≫
        (Functor.leftUnitor (F.pb c.i)).hom)
    (hp : (F.pbComp' tZ c.g (tZ ≫ c.g) rfl).hom ≫ Functor.whiskerLeft (F.pb c.g) τZ.hom ≫
        (Functor.rightUnitor (F.pb c.g)).hom =
      (F.pbComp' c.g tY (tZ ≫ c.g) hg.symm).hom ≫ Functor.whiskerRight τY.hom (F.pb c.g) ≫
        (Functor.leftUnitor (F.pb c.g)).hom) :
    (F.compIso (Compactification.Triangle.ofEndoLeft c tX tZ hX)).inv ≫
        Functor.whiskerRight (F.shriekOfIsProperTriv tX τX).hom (F.shriek c) ≫
        (Functor.leftUnitor _).hom =
      (F.compIso (Compactification.Triangle.ofEndoRight c tY tZ hg)).inv ≫
        Functor.whiskerLeft (F.shriek c) (F.shriekOfIsProperTriv tY τY).hom ≫
        (Functor.rightUnitor _).hom := by
  ext K
  have h := (F.map_shriekOfIsProperTriv_inv_app_comp_compIso_ofEndoLeft_hom_app c tX tZ τX τZ
    hX hi K).trans ((F.pfComp'_inv_of_triv_app tZ tY τZ τY c.g (tZ ≫ c.g) rfl hg.symm hp
      ((F.sh c.i).obj K)).trans
    (F.shriekOfIsProperTriv_inv_app_comp_compIso_ofEndoRight_hom_app c tY tZ τY hg K).symm)
  have e : (F.shriek c).mapIso ((F.shriekOfIsProperTriv tX τX).app K).symm ≪≫
      (F.compIso (Compactification.Triangle.ofEndoLeft c tX tZ hX)).app K =
      ((F.shriekOfIsProperTriv tY τY).app ((F.shriek c).obj K)).symm ≪≫
        (F.compIso (Compactification.Triangle.ofEndoRight c tY tZ hg)).app K :=
    Iso.ext h
  have e' := congrArg Iso.inv e
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv, Iso.app_hom] at e'
  simpa using e'

end Triangle

section Generic

variable {C D E : Type*} [Category C] [Category D] [Category E]

/-- Precomposing the horizontal composite of the inverses of `α : F' ≅ F` and `β : H' ≅ H` with
the whiskering of `α.hom ≫ ρ` along `H'`, for `ρ : F ⟶ 𝟭`, is the whiskering of `ρ` along `H`
followed by `β.inv`. -/
lemma hcomp_inv_comp_whiskerRight_comp_leftUnitor {F F' : C ⥤ C} {H H' : C ⥤ D} (α : F' ≅ F)
    (β : H' ≅ H) (ρ : F ⟶ 𝟭 C) :
    NatTrans.hcomp α.inv β.inv ≫ Functor.whiskerRight (α.hom ≫ ρ) H' ≫
        (Functor.leftUnitor H').hom =
      Functor.whiskerRight ρ H ≫ (Functor.leftUnitor H).hom ≫ β.inv := by
  ext K
  have h := β.inv.naturality (ρ.app K)
  simp only [Functor.id_obj] at h
  simp [NatTrans.hcomp_app, ← Functor.map_comp_assoc, h]

/-- Precomposing the horizontal composite of the inverses of `β : H' ≅ H` and `α : G' ≅ G` with
the whiskering of `α.hom ≫ ρ` along `H'`, for `ρ : G ⟶ 𝟭`, is the whiskering of `ρ` along `H`
followed by `β.inv`. -/
lemma hcomp_inv_comp_whiskerLeft_comp_rightUnitor {H H' : C ⥤ D} {G G' : D ⥤ D} (β : H' ≅ H)
    (α : G' ≅ G) (ρ : G ⟶ 𝟭 D) :
    NatTrans.hcomp β.inv α.inv ≫ Functor.whiskerLeft H' (α.hom ≫ ρ) ≫
        (Functor.rightUnitor H').hom =
      Functor.whiskerLeft H ρ ≫ (Functor.rightUnitor H).hom ≫ β.inv := by
  ext K
  have h := α.hom.naturality (β.inv.app K)
  have h' := ρ.naturality (β.inv.app K)
  simp only [Functor.id_obj, Functor.id_map] at h h'
  simp [NatTrans.hcomp_app, reassoc_of% h, h']

end Generic

section Canonical

variable {X Y : Scheme.{u}}

/-- The comparison isomorphism from the compactification `withEndo` of `f'` to the chosen
compactification, followed by the congruence `f' = f''`, is the comparison isomorphism from the
compactification `withEndo` of `f''`. -/
lemma shriekIso_withEndo_trans_lowerShriekCongr {f : X ⟶ Y} (c : Compactification f)
    (t : c.Z ⟶ c.Z) [IsProper t] {f' f'' : X ⟶ Y} [HasCompactification f']
    [HasCompactification f''] [QuasiCompact f'] [QuasiCompact f''] (h : f' = f'')
    (h' : f' = c.i ≫ t ≫ c.g) (h'' : f'' = c.i ≫ t ≫ c.g) :
    F.shriekIso (c.withEndo t h') (HasCompactification.compactification f') ≪≫
        F.lowerShriekCongr h =
      F.shriekIso (c.withEndo t h'') (HasCompactification.compactification f'') := by
  subst h
  rw [lowerShriekCongr_refl, Iso.trans_refl]

/-- **The composition isomorphisms of a trivialized square**: for `f : X ⟶ Y` and proper
endomorphisms `t_X`, `t_Y` with `t_X ≫ f = f ≫ t_Y` and trivialized pullbacks, the two maps
`(t_X ≫ f)_! = (f ≫ t_Y)_! ⟶ f_!` obtained from the composition isomorphisms
`F.lowerShriekCompIso` and the trivializations `F.lowerShriekTriv` agree, provided some
compactification `X ⟶[i] Z ⟶[g] Y` of `f` carries a proper endomorphism `t_Z` with cartesian
square `t_X ≫ i = i ≫ t_Z`, with `t_Z ≫ g = g ≫ t_Y`, and with a trivialization `τ_Z` such that
the trivializations are compatible with the pullbacks along `i` and `g`. -/
theorem lowerShriekCompIso_inv_triv {f : X ⟶ Y} (c : Compactification f) (tX : X ⟶ X)
    (tY : Y ⟶ Y) (tZ : c.Z ⟶ c.Z) [IsProper tX] [IsProper tY] [IsProper tZ]
    [HasCompactification f] [QuasiCompact f] [HasCompactification (tX ≫ f)]
    [QuasiCompact (tX ≫ f)] [HasCompactification (f ≫ tY)] [QuasiCompact (f ≫ tY)]
    (hf : tX ≫ f = f ≫ tY) (hX : IsPullback tX c.i c.i tZ) (hg : tZ ≫ c.g = c.g ≫ tY)
    (τX : F.pb tX ≅ 𝟭 (F.obj X)) (τY : F.pb tY ≅ 𝟭 (F.obj Y))
    (τZ : F.pb tZ ≅ 𝟭 (F.obj c.Z))
    (hi : (F.pbComp' tX c.i (tX ≫ c.i) rfl).hom ≫ Functor.whiskerLeft (F.pb c.i) τX.hom ≫
        (Functor.rightUnitor (F.pb c.i)).hom =
      (F.pbComp' c.i tZ (tX ≫ c.i) hX.w.symm).hom ≫ Functor.whiskerRight τZ.hom (F.pb c.i) ≫
        (Functor.leftUnitor (F.pb c.i)).hom)
    (hp : (F.pbComp' tZ c.g (tZ ≫ c.g) rfl).hom ≫ Functor.whiskerLeft (F.pb c.g) τZ.hom ≫
        (Functor.rightUnitor (F.pb c.g)).hom =
      (F.pbComp' c.g tY (tZ ≫ c.g) hg.symm).hom ≫ Functor.whiskerRight τY.hom (F.pb c.g) ≫
        (Functor.leftUnitor (F.pb c.g)).hom) :
    (F.lowerShriekCompIso tX f).inv ≫
        Functor.whiskerRight (F.lowerShriekTriv tX τX).hom (F.lowerShriek f) ≫
        (Functor.leftUnitor _).hom =
      (F.lowerShriekCongr hf).hom ≫ (F.lowerShriekCompIso f tY).inv ≫
        Functor.whiskerLeft (F.lowerShriek f) (F.lowerShriekTriv tY τY).hom ≫
        (Functor.rightUnitor _).hom := by
  have i₁ := congrArg Iso.inv
    (Iso.ext (F.lowerShriekCompIso_hom_eq (Compactification.Triangle.ofEndoLeft c tX tZ hX)) :
      F.lowerShriekCompIso tX f = NatIso.hcomp _ _ ≪≫
        F.compIso (Compactification.Triangle.ofEndoLeft c tX tZ hX) ≪≫ _)
  have i₂ := congrArg Iso.inv
    (Iso.ext (F.lowerShriekCompIso_hom_eq (Compactification.Triangle.ofEndoRight c tY tZ hg)) :
      F.lowerShriekCompIso f tY = NatIso.hcomp _ _ ≪≫
        F.compIso (Compactification.Triangle.ofEndoRight c tY tZ hg) ≪≫ _)
  simp only [Iso.trans_inv, NatIso.hcomp_inv] at i₁ i₂
  have eX : F.lowerShriekTriv tX τX =
      F.shriekIso _ (Compactification.Triangle.ofEndoLeft c tX tZ hX).cf ≪≫
        F.shriekOfIsProperTriv tX τX := rfl
  have eY : F.lowerShriekTriv tY τY =
      F.shriekIso _ (Compactification.Triangle.ofEndoRight c tY tZ hg).cg ≪≫
        F.shriekOfIsProperTriv tY τY := rfl
  have hS : (F.lowerShriekCongr hf).hom ≫
      (F.shriekIso (Compactification.Triangle.ofEndoRight c tY tZ hg).cfg
        (HasCompactification.compactification (f ≫ tY))).inv =
      (F.shriekIso (Compactification.Triangle.ofEndoLeft c tX tZ hX).cfg
        (HasCompactification.compactification (tX ≫ f))).inv := by
    have h := congrArg Iso.inv (F.shriekIso_withEndo_trans_lowerShriekCongr c tZ hf
      (Compactification.Triangle.ofEndoLeft c tX tZ hX).cfg.comm
      (Compactification.Triangle.ofEndoRight c tY tZ hg).cfg.comm)
    rw [Iso.trans_inv] at h
    calc _ = (F.lowerShriekCongr hf).hom ≫ ((F.lowerShriekCongr hf).inv ≫
          (F.shriekIso (Compactification.Triangle.ofEndoLeft c tX tZ hX).cfg
            (HasCompactification.compactification (tX ≫ f))).inv) :=
        congrArg _ h.symm
      _ = _ := Iso.hom_inv_id_assoc _ _
  rw [i₁, i₂, eX, eY, Iso.trans_hom, Iso.trans_hom]
  simp only [Category.assoc]
  rw [hcomp_inv_comp_whiskerRight_comp_leftUnitor, hcomp_inv_comp_whiskerLeft_comp_rightUnitor,
    reassoc_of% hS]
  have h := congrArg (fun x ↦
    (F.shriekIso (Compactification.Triangle.ofEndoLeft c tX tZ hX).cfg
      (HasCompactification.compactification (tX ≫ f))).inv ≫ x ≫
      (F.shriekIso (HasCompactification.compactification f) c).inv)
    (F.compIso_inv_ofEndo c tX tY tZ τX τY τZ hX hg hi hp)
  simp only [Category.assoc] at h
  exact h

end Canonical

end CompactSupportFormalism

end AlgebraicGeometry
