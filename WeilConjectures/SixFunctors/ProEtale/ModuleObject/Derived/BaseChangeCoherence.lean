/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BaseChangePaste
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPasteLaws
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

/-!
# Naturality, identity and pasting of the pro-étale base change map

For a commutative square `g' ≫ f = f' ≫ g` of schemes, the pro-étale base change map
`Lg^* Rf_* ⟶ Rf'_* Lg'^*` (`ProEtale.CondensedRing.baseChangeMap`) on the unbounded derived
categories of module objects over a condensed ring `Λ`:

- is natural in `K` (`ProEtale.CondensedRing.baseChangeMap_naturality`);
- is the identity for an identity square, through `L(𝟙)^* ≅ 𝟭`
  (`ProEtale.CondensedRing.baseChangeMap_app_id`);
- is compatible with horizontal pasting (`ProEtale.CondensedRing.baseChangeMap_app_paste_horiz`)
  and with vertical pasting (`ProEtale.CondensedRing.baseChangeMap_app_paste_vert`), through
  the composition isomorphisms of derived pullbacks and pushforwards.

## Implementation details

The formal parts are the abstract statements `CategoryTheory.mateEquiv_app_of_isoId`,
`CategoryTheory.Adjunction.exchangeRight_app_paste_of_eq` and
`CategoryTheory.Adjunction.exchangeRight_app_paste_vert` about mates and exchange morphisms
(`WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPasteLaws`).

`ProEtale.CondensedRing.baseChangeMap_eq_exchangeRight` is proved by unfolding `baseChangeMap`:
its instance arguments were elaborated in another context, and comparing them at default
transparency times out.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj CategoryTheory.Functor

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
comparison. -/
lemma baseChangeMap_eq_exchangeRight (sq : CommSq g' f' f g) :
    baseChangeMap Λ sq = Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ f)
      (derivedUpperStarLowerStarAdjunction Λ f') (pullbackSquareComparison Λ sq) := by
  delta baseChangeMap
  with_reducible_and_instances rfl

/-- For a commutative square
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

/-- The pro-étale base change map of the square with vertical maps `f, f` and horizontal maps
`𝟙 X, 𝟙 Y`
```
X --𝟙--> X
|f       |f
v        v
Y --𝟙--> Y
```
is the composite `L(𝟙 Y)^* Rf_* K ≅ Rf_* K ≅ Rf_* L(𝟙 X)^* K` of the identity isomorphisms of the
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

/-- Horizontal pasting: for two horizontally pasted commutative squares
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

/-- Vertical pasting: for two vertically pasted commutative squares
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
