/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BaseChangePaste
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

/-!
# Naturality, identity and pasting of the pro-étale base change map

For a commutative square `g' ≫ f = f' ≫ g` of schemes, the pro-étale base change map
`Lg^* Rf_* ⟶ Rf'_* Lg'^*` (`ProEtale.CondensedRing.baseChangeMap`, blueprint
`definition-pro-etale-base-change-map`) on the unbounded derived categories of module objects over
a condensed ring `Λ`:

- is natural in `K` (`ProEtale.CondensedRing.baseChangeMap_naturality`);
- is the identity for an identity square, through `L(𝟙)^* ≅ 𝟭`
  (`ProEtale.CondensedRing.baseChangeMap_app_id`);
- is compatible with horizontal pasting (`ProEtale.CondensedRing.baseChangeMap_app_paste_horiz`)
  and with vertical pasting (`ProEtale.CondensedRing.baseChangeMap_app_paste_vert`), through
  the composition isomorphisms of derived pullbacks and pushforwards.

These are blueprint `lemma-naturality-pasting-comparison--1` and
`lemma-naturality-pasting-comparison--2`, in the form of `lemma-identity-pasting`. The formal
parts are the abstract statements `CategoryTheory.mateEquiv_app_of_isoId`,
`CategoryTheory.Adjunction.exchangeRight_app_paste_of_eq` and
`CategoryTheory.Adjunction.exchangeRight_app_paste_vert` about mates and exchange morphisms.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

/-- The mate of a transformation `θ : G ⋙ L ⟶ L ⋙ H` of the form `L(I₁) ≫ I₂⁻¹`, for isomorphisms
`I₁ : G ≅ 𝟭` and `I₂ : H ≅ 𝟭`, is `I₁(R) ≫ R(I₂⁻¹)`. -/
lemma mateEquiv_app_of_isoId {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {G : C ⥤ C} {H : D ⥤ D} (I₁ : G ≅ 𝟭 C) (I₂ : H ≅ 𝟭 D) (θ : G ⋙ L ⟶ L ⋙ H)
    (hθ : ∀ B, θ.app B = L.map (I₁.hom.app B) ≫ I₂.inv.app (L.obj B)) (Y : D) :
    (mateEquiv a a θ).natTrans.app Y = I₁.hom.app (R.obj Y) ≫ R.map (I₂.inv.app Y) := by
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
and by the inverse of `c'`. -/
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
namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option hygiene false in
/-- The derived category `D(X_proét, Λ) = D(Mod_{Λ_X})` of module objects over `Λ_X`. -/
local notation "𝔻(" X ")" =>
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Square

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The base change map of module objects is the exchange morphism of the pullback square
comparison. The two sides only differ by the unfolding of `baseChangeMap`, whose instance
arguments were elaborated in another context (comparing them at default transparency times
out). -/
lemma baseChangeMap_eq_exchangeRight (sq : CommSq g' f' f g) :
    baseChangeMap Λ sq = Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ f)
      (derivedUpperStarLowerStarAdjunction Λ f') (pullbackSquareComparison Λ sq) := by
  delta baseChangeMap
  with_reducible_and_instances rfl

/-- Blueprint `lemma-naturality-pasting-comparison--1`: for a commutative square
`g' ≫ f = f' ≫ g`, the pro-étale base change maps `Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` on the unbounded
derived categories are natural in `K`. -/
lemma baseChangeMap_naturality (sq : CommSq g' f' f g) {K K' : 𝔻(X)} (φ : K ⟶ K') :
    L((g)^*⟦Λ⟧).map (R((f)_*⟦Λ⟧).map φ) ≫ (baseChangeMap Λ sq).app K' =
      (baseChangeMap Λ sq).app K ≫ R((f')_*⟦Λ⟧).map (L((g')^*⟦Λ⟧).map φ) :=
  (baseChangeMap Λ sq).naturality φ

end Square

section Identity

variable {X Y : Scheme.{u}}

/-- The pullback comparison `Lp^* L(𝟙)^* ≅ L(𝟙)^* Lp^*` of the square `p ≫ 𝟙 = 𝟙 ≫ p` is
`I ≫ Lp^*(I⁻¹)`, for the identity isomorphisms `I : L(𝟙)^* ≅ 𝟭`. -/
lemma pullbackSquareComparison_hom_app_id_right (p : X ⟶ Y)
    (sq : CommSq p (𝟙 X) (𝟙 Y) p)
    (B : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (pullbackSquareComparison Λ sq).hom.app B =
      (leftDerivedUpperStarId Λ X).hom.app (L((p)^*⟦Λ⟧).obj B) ≫
        L((p)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Y).inv.app B) := by
  have h₁ := leftDerivedUpperStarComp_id_left_app Λ p B
  have h₂ := leftDerivedUpperStarComp_id_right_app Λ p B
  simp only [pullbackSquareComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app]
  rw [← cancel_epi ((leftDerivedUpperStarComp Λ (𝟙 X) p).hom.app B), Iso.hom_inv_id_app_assoc,
    reassoc_of% h₁]
  rw [← cancel_mono (L((p)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Y).hom.app B))]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, h₂, eqToHom_trans]
  simp

/-- The pullback comparison `L(𝟙)^* Lp^* ≅ Lp^* L(𝟙)^*` of the square `𝟙 ≫ p = p ≫ 𝟙` is
`Lp^*(I) ≫ I⁻¹`, for the identity isomorphisms `I : L(𝟙)^* ≅ 𝟭`. -/
lemma pullbackSquareComparison_hom_app_id_left (p : X ⟶ Y)
    (sq : CommSq (𝟙 X) p p (𝟙 Y))
    (B : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (pullbackSquareComparison Λ sq).hom.app B =
      L((p)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Y).hom.app B) ≫
        (leftDerivedUpperStarId Λ X).inv.app (L((p)^*⟦Λ⟧).obj B) := by
  have h₁ := leftDerivedUpperStarComp_id_left_app Λ p B
  have h₂ := leftDerivedUpperStarComp_id_right_app Λ p B
  simp only [pullbackSquareComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app]
  rw [← cancel_epi ((leftDerivedUpperStarComp Λ p (𝟙 Y)).hom.app B), Iso.hom_inv_id_app_assoc,
    reassoc_of% h₂]
  rw [← cancel_mono ((leftDerivedUpperStarId Λ X).hom.app (L((p)^*⟦Λ⟧).obj B))]
  simp only [Category.assoc, Iso.inv_hom_id_app, h₁, eqToHom_trans]
  simp

/-- Blueprint `lemma-naturality-pasting-comparison--2`, identity square: the pro-étale base
change map of the square with vertical maps `f, f` and horizontal maps `𝟙 X, 𝟙 Y` is the
composite `L(𝟙 Y)^* Rf_* K ≅ Rf_* K ≅ Rf_* L(𝟙 X)^* K` of the identity isomorphisms of the
derived pullbacks. -/
lemma baseChangeMap_app_id (f : X ⟶ Y) (sq : CommSq (𝟙 X) f f (𝟙 Y)) (K : 𝔻(X)) :
    (baseChangeMap Λ sq).app K =
      (leftDerivedUpperStarId Λ Y).hom.app (R((f)_*⟦Λ⟧).obj K) ≫
        R((f)_*⟦Λ⟧).map ((leftDerivedUpperStarId Λ X).inv.app K) :=
  (congrArg (fun t ↦ t.app K) ((baseChangeMap_eq_exchangeRight Λ sq).trans
    (Adjunction.exchangeRight_eq_mateEquiv _ _ _))).trans
    (mateEquiv_app_of_isoId (derivedUpperStarLowerStarAdjunction Λ f) (leftDerivedUpperStarId Λ Y)
      (leftDerivedUpperStarId Λ X) (pullbackSquareComparison Λ sq).hom
      (pullbackSquareComparison_hom_app_id_left Λ f sq) K)

end Identity

section Horizontal

variable {X Y X' Y' X'' Y'' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'} {f'' : X'' ⟶ Y''}

/-- Blueprint `lemma-naturality-pasting-comparison--2`, horizontal pasting: for two horizontally
pasted commutative squares
```
X'' --h'--> X' --g'--> X
 |f''       |f'        |f
 v          v          v
Y'' --h---> Y' --g---> Y
```
the pro-étale base change map of the outer square is the composite
`L(h ≫ g)^* Rf_* K ≅ Lh^* Lg^* Rf_* K ⟶ Lh^* Rf'_* Lg'^* K ⟶ Rf''_* Lh'^* Lg'^* K ≅
Rf''_* L(h' ≫ g')^* K`. -/
lemma baseChangeMap_app_paste_horiz (sq₁ : CommSq g' f' f g) (sq₂ : CommSq h' f'' f' h)
    (sq : CommSq (h' ≫ g') f'' f (h ≫ g)) (K : 𝔻(X)) :
    (leftDerivedUpperStarComp Λ h g).hom.app (R((f)_*⟦Λ⟧).obj K) ≫
        L((h)^*⟦Λ⟧).map ((baseChangeMap Λ sq₁).app K) ≫
        (baseChangeMap Λ sq₂).app (L((g')^*⟦Λ⟧).obj K) ≫
        R((f'')_*⟦Λ⟧).map ((leftDerivedUpperStarComp Λ h' g').inv.app K) =
      (baseChangeMap Λ sq).app K :=
  Adjunction.exchangeRight_app_paste_of_eq (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f') (derivedUpperStarLowerStarAdjunction Λ f'')
    (pullbackSquareComparison Λ sq₁) (pullbackSquareComparison Λ sq₂)
    (pullbackSquareComparison Λ sq) (leftDerivedUpperStarComp Λ h g)
    (leftDerivedUpperStarComp Λ h' g') (pullbackSquareComparison_paste Λ sq₁ sq₂ sq)
    (baseChangeMap Λ sq₁) (baseChangeMap Λ sq₂) (baseChangeMap Λ sq)
    (baseChangeMap_eq_exchangeRight Λ sq₁) (baseChangeMap_eq_exchangeRight Λ sq₂)
    (baseChangeMap_eq_exchangeRight Λ sq) K

end Horizontal

section Vertical

variable {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z' ⟶ Z} {hY : Y' ⟶ Y}
  {g' : Y' ⟶ Z'} {hX : X' ⟶ X} {f' : X' ⟶ Y'}

/-- Blueprint `lemma-naturality-pasting-comparison--2`, vertical pasting: for two vertically
pasted commutative squares
```
X' --hX--> X
|f'        |f
v          v
Y' --hY--> Y
|g'        |g
v          v
Z' --h---> Z
```
the pro-étale base change map of the outer square is the composite
`Lh^* R(f ≫ g)_* K ≅ Lh^* Rg_* Rf_* K ⟶ Rg'_* LhY^* Rf_* K ⟶ Rg'_* Rf'_* LhX^* K ≅
R(f' ≫ g')_* LhX^* K` of the base change map of the lower square at `Rf_* K` and `Rg'_*` of the
base change map of the upper square at `K`. -/
lemma baseChangeMap_app_paste_vert (sq₁ : CommSq hY g' g h) (sq₂ : CommSq hX f' f hY)
    (sq : CommSq hX (f' ≫ g') (f ≫ g) h) (K : 𝔻(X)) :
    L((h)^*⟦Λ⟧).map ((rightDerivedLowerStarComp Λ f g).inv.app K) ≫
        (baseChangeMap Λ sq₁).app (R((f)_*⟦Λ⟧).obj K) ≫
        R((g')_*⟦Λ⟧).map ((baseChangeMap Λ sq₂).app K) ≫
        (rightDerivedLowerStarComp Λ f' g').hom.app (L((hX)^*⟦Λ⟧).obj K) =
      (baseChangeMap Λ sq).app K :=
  Adjunction.exchangeRight_app_paste_vert (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ g) (derivedUpperStarLowerStarAdjunction Λ (f ≫ g))
    (derivedUpperStarLowerStarAdjunction Λ f') (derivedUpperStarLowerStarAdjunction Λ g')
    (derivedUpperStarLowerStarAdjunction Λ (f' ≫ g')) (pullbackSquareComparison Λ sq₁)
    (pullbackSquareComparison Λ sq₂) (pullbackSquareComparison Λ sq)
    (leftDerivedUpperStarComp Λ f g) (leftDerivedUpperStarComp Λ f' g')
    (rightDerivedLowerStarComp Λ f g) (rightDerivedLowerStarComp Λ f' g')
    (pullbackSquareComparison Λ sq₁.flip) (pullbackSquareComparison Λ sq₂.flip)
    (pullbackSquareComparison Λ sq.flip) (pullbackSquareComparison_flip Λ sq₁)
    (pullbackSquareComparison_flip Λ sq₂) (pullbackSquareComparison_flip Λ sq)
    (pullbackSquareComparison_paste Λ sq₁.flip sq₂.flip sq.flip)
    (fun M ↦ (conjugateEquiv_counit _ _ _ M).trans (by rw [Adjunction.comp_counit_app]; rfl))
    (fun M ↦ (conjugateEquiv_counit _ _ _ M).trans (by rw [Adjunction.comp_counit_app]; rfl))
    (baseChangeMap Λ sq₁) (baseChangeMap Λ sq₂) (baseChangeMap Λ sq)
    (baseChangeMap_eq_exchangeRight Λ sq₁) (baseChangeMap_eq_exchangeRight Λ sq₂)
    (baseChangeMap_eq_exchangeRight Λ sq) K

end Vertical

end AlgebraicGeometry.ProEtale.CondensedRing
