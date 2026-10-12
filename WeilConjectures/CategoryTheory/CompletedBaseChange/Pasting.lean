/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.CompletedBaseChange.Completed

/-!
# Identity and pasting laws for exchange maps

For base change squares (`CategoryTheory.BaseChangeSquare`) we define

* the identity square `BaseChangeSquare.id adj` of an adjunction `f^* ⊣ f_*` (`g = 𝟙`);
* the horizontal pasting `𝔇.hcomp …` along the pullback direction (`Y'' → Y' → Y`);
* the vertical pasting `𝔇.vcomp …` along the proper direction (`X → Y → Z`),

and prove the identity and pasting laws of exchange maps (the finite-level S0/S8 equations):
the exchange map of an identity square is the identity, and the exchange map of a pasted square
is the composite of the exchange maps (`exchange_id`, `exchange_hcomp`, `exchange_vcomp`). They
are instances of the compatibility of the mate correspondence with composition of squares.

Since the completed exchange map is the derived limit of the tower exchange maps conjugated by
fixed isomorphisms, these laws pass to the completed exchange map
(`lemma-weil-pbc-completed-exchange-coherence`): see
`CategoryTheory.BaseChangeSquare.CompletionDatum.completedExchange_app_of_id`,
`completedExchange_app_of_hcomp` and `completedExchange_app_of_vcomp`; the naturality in `K` is
`CompletionDatum.completedExchange_naturality`.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open CategoryTheory CategoryTheory.Functor CategoryTheory.TwoSquare

namespace CategoryTheory

namespace BaseChangeSquare

section Laws

variable {𝒳 : Type u₁} {𝒴 : Type u₂} {𝒳' : Type u₃} {𝒴' : Type u₄}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒴] [Category.{v₃} 𝒳'] [Category.{v₄} 𝒴']

/-- The identity base change square of an adjunction `f^* ⊣ f_*`: `g = 𝟙`, `g' = 𝟙`,
`f' = f`, with the unitors as Cartesian identification. -/
@[simps]
def id {upperF : 𝒴 ⥤ 𝒳} {lowerF : 𝒳 ⥤ 𝒴} (adj : upperF ⊣ lowerF) :
    BaseChangeSquare 𝒳 𝒴 𝒳 𝒴 where
  upperF := upperF
  lowerF := lowerF
  adjF := adj
  upperF' := upperF
  lowerF' := lowerF
  adjF' := adj
  upperG := 𝟭 _
  upperG' := 𝟭 _
  iso := Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm

/-- **Identity law**: the exchange map of an identity square is the identity. -/
lemma exchange_id {upperF : 𝒴 ⥤ 𝒳} {lowerF : 𝒳 ⥤ 𝒴} (adj : upperF ⊣ lowerF) (K : 𝒳) :
    (id adj).exchange.natTrans.app K = 𝟙 _ := by
  change (mateEquiv adj adj (TwoSquare.mk (𝟭 𝒴) upperF upperF (𝟭 𝒳)
    ((Functor.leftUnitor upperF).hom ≫ (Functor.rightUnitor upperF).inv))).natTrans.app K = _
  rw [mateEquiv_unitors]
  simp

variable {𝒳'' : Type u₅} {𝒴'' : Type u₆} [Category.{v₅} 𝒳''] [Category.{v₆} 𝒴'']

/-- The square `X'' → X'` over `Y'' → Y'` to be pasted to the right of `𝔇`: its left side is
the right side `f'^* ⊣ f'_*` of `𝔇`. -/
@[simps]
def right (𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴') {upperF'' : 𝒴'' ⥤ 𝒳''} {lowerF'' : 𝒳'' ⥤ 𝒴''}
    (adjF'' : upperF'' ⊣ lowerF'') (upperG₂ : 𝒴' ⥤ 𝒴'') (upperG₂' : 𝒳' ⥤ 𝒳'')
    (iso₂ : upperG₂ ⋙ upperF'' ≅ 𝔇.upperF' ⋙ upperG₂') :
    BaseChangeSquare 𝒳' 𝒴' 𝒳'' 𝒴'' where
  upperF := 𝔇.upperF'
  lowerF := 𝔇.lowerF'
  adjF := 𝔇.adjF'
  upperF' := upperF''
  lowerF' := lowerF''
  adjF' := adjF''
  upperG := upperG₂
  upperG' := upperG₂'
  iso := iso₂

/-- **Horizontal pasting** of `𝔇` with a square `X'' → X'` over `Y'' → Y'`: the square
`X'' → X` over `Y'' → Y` with pullbacks `g^* ⋙ g₂^*`, `g'^* ⋙ g₂'^*`. -/
@[simps]
def hcomp (𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴') {upperF'' : 𝒴'' ⥤ 𝒳''} {lowerF'' : 𝒳'' ⥤ 𝒴''}
    (adjF'' : upperF'' ⊣ lowerF'') (upperG₂ : 𝒴' ⥤ 𝒴'') (upperG₂' : 𝒳' ⥤ 𝒳'')
    (iso₂ : upperG₂ ⋙ upperF'' ≅ 𝔇.upperF' ⋙ upperG₂') :
    BaseChangeSquare 𝒳 𝒴 𝒳'' 𝒴'' where
  upperF := 𝔇.upperF
  lowerF := 𝔇.lowerF
  adjF := 𝔇.adjF
  upperF' := upperF''
  lowerF' := lowerF''
  adjF' := adjF''
  upperG := 𝔇.upperG ⋙ upperG₂
  upperG' := 𝔇.upperG' ⋙ upperG₂'
  iso := Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ iso₂ ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight 𝔇.iso _ ≪≫
      Functor.associator _ _ _

/-- **Horizontal pasting law**: the exchange map of the pasted square is the composite of the
exchange maps, `ξ_{□₂ ∘ □₁} = ξ_{□₂} g'^* ∘ g₂^* ξ_{□₁}`. -/
lemma exchange_hcomp (𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴') {upperF'' : 𝒴'' ⥤ 𝒳''}
    {lowerF'' : 𝒳'' ⥤ 𝒴''} (adjF'' : upperF'' ⊣ lowerF'') (upperG₂ : 𝒴' ⥤ 𝒴'')
    (upperG₂' : 𝒳' ⥤ 𝒳'') (iso₂ : upperG₂ ⋙ upperF'' ≅ 𝔇.upperF' ⋙ upperG₂') :
    (𝔇.hcomp adjF'' upperG₂ upperG₂' iso₂).exchange =
      𝔇.exchange ≫ᵥ (𝔇.right adjF'' upperG₂ upperG₂' iso₂).exchange :=
  mateEquiv_vcomp 𝔇.adjF 𝔇.adjF' adjF'' 𝔇.isoSquare
    (𝔇.right adjF'' upperG₂ upperG₂' iso₂).isoSquare

lemma exchange_hcomp_app (𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴') {upperF'' : 𝒴'' ⥤ 𝒳''}
    {lowerF'' : 𝒳'' ⥤ 𝒴''} (adjF'' : upperF'' ⊣ lowerF'') (upperG₂ : 𝒴' ⥤ 𝒴'')
    (upperG₂' : 𝒳' ⥤ 𝒳'') (iso₂ : upperG₂ ⋙ upperF'' ≅ 𝔇.upperF' ⋙ upperG₂') (K : 𝒳) :
    (𝔇.hcomp adjF'' upperG₂ upperG₂' iso₂).exchange.natTrans.app K =
      upperG₂.map (𝔇.exchange.natTrans.app K) ≫
        (𝔇.right adjF'' upperG₂ upperG₂' iso₂).exchange.natTrans.app (𝔇.upperG'.obj K) := by
  rw [exchange_hcomp]
  simp [TwoSquare.vComp]
  exact Category.id_comp _

variable {𝒵 : Type u₇} {𝒵' : Type u₈} [Category.{v₇} 𝒵] [Category.{v₈} 𝒵']

/-- The square `Y' → Y` over `Z' → Z` to be pasted below `𝔇`: its pullback on top is the
pullback `g^*` of `𝔇`. -/
@[simps]
def below (𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴') {upperH : 𝒵 ⥤ 𝒴} {lowerH : 𝒴 ⥤ 𝒵}
    (adjH : upperH ⊣ lowerH) {upperH' : 𝒵' ⥤ 𝒴'} {lowerH' : 𝒴' ⥤ 𝒵'}
    (adjH' : upperH' ⊣ lowerH') (upperGZ : 𝒵 ⥤ 𝒵')
    (iso₀ : upperGZ ⋙ upperH' ≅ upperH ⋙ 𝔇.upperG) :
    BaseChangeSquare 𝒴 𝒵 𝒴' 𝒵' where
  upperF := upperH
  lowerF := lowerH
  adjF := adjH
  upperF' := upperH'
  lowerF' := lowerH'
  adjF' := adjH'
  upperG := upperGZ
  upperG' := 𝔇.upperG
  iso := iso₀

/-- **Vertical pasting** of `𝔇` with a square `Y' → Y` over `Z' → Z`: the square `X' → X` over
`Z' → Z` for the composites `X → Y → Z`, with `(h ∘ f)^* = f^* ∘ h^*` and
`(h ∘ f)_* = h_* ∘ f_*`. -/
@[simps]
def vcomp (𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴') {upperH : 𝒵 ⥤ 𝒴} {lowerH : 𝒴 ⥤ 𝒵}
    (adjH : upperH ⊣ lowerH) {upperH' : 𝒵' ⥤ 𝒴'} {lowerH' : 𝒴' ⥤ 𝒵'}
    (adjH' : upperH' ⊣ lowerH') (upperGZ : 𝒵 ⥤ 𝒵')
    (iso₀ : upperGZ ⋙ upperH' ≅ upperH ⋙ 𝔇.upperG) :
    BaseChangeSquare 𝒳 𝒵 𝒳' 𝒵' where
  upperF := upperH ⋙ 𝔇.upperF
  lowerF := 𝔇.lowerF ⋙ lowerH
  adjF := adjH.comp 𝔇.adjF
  upperF' := upperH' ⋙ 𝔇.upperF'
  lowerF' := 𝔇.lowerF' ⋙ lowerH'
  adjF' := adjH'.comp 𝔇.adjF'
  upperG := upperGZ
  upperG' := 𝔇.upperG'
  iso := (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight iso₀ _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ 𝔇.iso ≪≫
      (Functor.associator _ _ _).symm

/-- **Vertical pasting law**: the exchange map of the vertically pasted square is the composite
`h'_* ξ_{□} ∘ ξ_{□₀} f_*` of the exchange maps. -/
lemma exchange_vcomp (𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴') {upperH : 𝒵 ⥤ 𝒴} {lowerH : 𝒴 ⥤ 𝒵}
    (adjH : upperH ⊣ lowerH) {upperH' : 𝒵' ⥤ 𝒴'} {lowerH' : 𝒴' ⥤ 𝒵'}
    (adjH' : upperH' ⊣ lowerH') (upperGZ : 𝒵 ⥤ 𝒵')
    (iso₀ : upperGZ ⋙ upperH' ≅ upperH ⋙ 𝔇.upperG) :
    (𝔇.vcomp adjH adjH' upperGZ iso₀).exchange =
      𝔇.exchange ≫ₕ (𝔇.below adjH adjH' upperGZ iso₀).exchange :=
  mateEquiv_hcomp adjH adjH' 𝔇.adjF 𝔇.adjF' (𝔇.below adjH adjH' upperGZ iso₀).isoSquare
    𝔇.isoSquare

lemma exchange_vcomp_app (𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴') {upperH : 𝒵 ⥤ 𝒴}
    {lowerH : 𝒴 ⥤ 𝒵} (adjH : upperH ⊣ lowerH) {upperH' : 𝒵' ⥤ 𝒴'} {lowerH' : 𝒴' ⥤ 𝒵'}
    (adjH' : upperH' ⊣ lowerH') (upperGZ : 𝒵 ⥤ 𝒵')
    (iso₀ : upperGZ ⋙ upperH' ≅ upperH ⋙ 𝔇.upperG) (K : 𝒳) :
    (𝔇.vcomp adjH adjH' upperGZ iso₀).exchange.natTrans.app K =
      (𝔇.below adjH adjH' upperGZ iso₀).exchange.natTrans.app (𝔇.lowerF.obj K) ≫
        lowerH'.map (𝔇.exchange.natTrans.app K) := by
  rw [exchange_vcomp]
  simp [TwoSquare.hComp]
  exact Category.id_comp _

end Laws

section Completed

open Limits

variable {𝒳 : Type u₁} {𝒴 : Type u₂} {𝒳' : Type u₃} {𝒴' : Type u₄}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒴] [Category.{v₃} 𝒳'] [Category.{v₄} 𝒴']
  {𝒯 : Type u₅} {𝒰 : Type u₆} {𝒯' : Type u₇} {𝒰' : Type u₈}
  [Category.{v₅} 𝒯] [Category.{v₆} 𝒰] [Category.{v₇} 𝒯'] [Category.{v₈} 𝒰']
  [HasZeroObject 𝒳'] [HasShift 𝒳' ℤ] [Preadditive 𝒳']
  [∀ n : ℤ, (shiftFunctor 𝒳' n).Additive] [Pretriangulated 𝒳']
  [HasZeroObject 𝒴'] [HasShift 𝒴' ℤ] [Preadditive 𝒴']
  [∀ n : ℤ, (shiftFunctor 𝒴' n).Additive] [Pretriangulated 𝒴']


namespace CompletionDatum

variable {𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴'}

/-- **Naturality of completed exchange** (Blueprint
`lemma-weil-pbc-completed-exchange-coherence`, first assertion): `Ex^comp` is natural in `K`. -/
@[reassoc]
lemma completedExchange_naturality {𝔗 : BaseChangeSquare 𝒯 𝒰 𝒯' 𝒰'}
    (𝔠 : CompletionDatum 𝔇 𝔗) {K L : 𝒳} (φ : K ⟶ L) :
    (𝔇.lowerF ⋙ 𝔠.completedPullback).map φ ≫ 𝔠.completedExchange.app L =
      𝔠.completedExchange.app K ≫ (𝔠.completedPullback' ⋙ 𝔇.lowerF').map φ :=
  𝔠.completedExchange.naturality φ

/-- **Identity law for completed exchange** (Blueprint
`lemma-weil-pbc-completed-exchange-coherence`): if the tower square is an identity square, the
completed exchange map is the canonical identification
`R lim A_• ⟶ R lim B_• = R lim D_• ≅ Rf'_* R lim K_•` built from the projection formula and the
direct-image/limit commutation alone. -/
lemma completedExchange_app_of_id {upperF : 𝒰 ⥤ 𝒯} {lowerF : 𝒯 ⥤ 𝒰} {adj : upperF ⊣ lowerF}
    (𝔠 : CompletionDatum 𝔇 (BaseChangeSquare.id adj)) (K : 𝒳) :
    𝔠.completedExchange.app K = 𝔠.limY'.rlim.map (𝔠.ρ.arrowH.app K) ≫
      𝔠.lowerLim.inv.app ((BaseChangeSquare.id adj).upperG'.obj (𝔠.ρ.redX.obj K)) := by
  rw [completedExchange_app, Reduction.arrowV'_app, exchange_id, Functor.map_id,
    Category.id_comp]

variable {𝒯'' : Type*} {𝒰'' : Type*} [Category 𝒯''] [Category 𝒰'']

/-- **Horizontal pasting law for completed exchange** (Blueprint
`lemma-weil-pbc-completed-exchange-coherence`): if the tower square is a horizontally pasted
square, the completed exchange map is the derived limit of the composite of the two tower
exchange maps, conjugated by the same isomorphisms. -/
lemma completedExchange_app_of_hcomp (𝔗₁ : BaseChangeSquare 𝒯 𝒰 𝒯'' 𝒰'')
    {upperF' : 𝒰' ⥤ 𝒯'} {lowerF' : 𝒯' ⥤ 𝒰'} {adjF' : upperF' ⊣ lowerF'} {G₂ : 𝒰'' ⥤ 𝒰'}
    {G₂' : 𝒯'' ⥤ 𝒯'} {iso₂ : G₂ ⋙ upperF' ≅ 𝔗₁.upperF' ⋙ G₂'}
    (𝔠 : CompletionDatum 𝔇 (𝔗₁.hcomp adjF' G₂ G₂' iso₂)) (K : 𝒳) :
    𝔠.completedExchange.app K = 𝔠.limY'.rlim.map (𝔠.ρ.arrowH.app K) ≫
      𝔠.limY'.rlim.map (G₂.map (𝔗₁.exchange.natTrans.app (𝔠.ρ.redX.obj K))) ≫
      𝔠.limY'.rlim.map ((𝔗₁.right adjF' G₂ G₂' iso₂).exchange.natTrans.app
        (𝔗₁.upperG'.obj (𝔠.ρ.redX.obj K))) ≫
      𝔠.lowerLim.inv.app ((𝔗₁.hcomp adjF' G₂ G₂' iso₂).upperG'.obj (𝔠.ρ.redX.obj K)) := by
  rw [completedExchange_app, Reduction.arrowV'_app, exchange_hcomp_app, Functor.map_comp,
    Category.assoc]

/-- **Vertical pasting law for completed exchange** (Blueprint
`lemma-weil-pbc-completed-exchange-coherence`): if the tower square is a vertically pasted
square, the completed exchange map is the derived limit of the composite of the two tower
exchange maps, conjugated by the same isomorphisms. -/
lemma completedExchange_app_of_vcomp (𝔗₁ : BaseChangeSquare 𝒯 𝒰'' 𝒯' 𝒰'')
    {upperH : 𝒰 ⥤ 𝒰''} {lowerH : 𝒰'' ⥤ 𝒰} {adjH : upperH ⊣ lowerH}
    {upperH' : 𝒰' ⥤ 𝒰''} {lowerH' : 𝒰'' ⥤ 𝒰'} {adjH' : upperH' ⊣ lowerH'}
    {upperGZ : 𝒰 ⥤ 𝒰'} {iso₀ : upperGZ ⋙ upperH' ≅ upperH ⋙ 𝔗₁.upperG}
    (𝔠 : CompletionDatum 𝔇 (𝔗₁.vcomp adjH adjH' upperGZ iso₀)) (K : 𝒳) :
    𝔠.completedExchange.app K = 𝔠.limY'.rlim.map (𝔠.ρ.arrowH.app K) ≫
      𝔠.limY'.rlim.map ((𝔗₁.below adjH adjH' upperGZ iso₀).exchange.natTrans.app
        (𝔗₁.lowerF.obj (𝔠.ρ.redX.obj K))) ≫
      𝔠.limY'.rlim.map (lowerH'.map (𝔗₁.exchange.natTrans.app (𝔠.ρ.redX.obj K))) ≫
      𝔠.lowerLim.inv.app ((𝔗₁.vcomp adjH adjH' upperGZ iso₀).upperG'.obj
        (𝔠.ρ.redX.obj K)) := by
  rw [completedExchange_app, Reduction.arrowV'_app, exchange_vcomp_app, Functor.map_comp,
    Category.assoc]

end CompletionDatum

end Completed

end BaseChangeSquare

end CategoryTheory
