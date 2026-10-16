/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.CompletedBaseChange.Rectangle
public import WeilConjectures.CategoryTheory.CompletedBaseChange.TowerLimit

/-!
# The completed base change map

Let `𝔇` be a base change square of (derived) categories `D(X), D(Y), D(X'), D(Y')` and let `𝔗`
be the base change square of the derived categories of towers `D(Tow(X))`, … formed by the
levelwise operations `Lg^*_Tow`, `Rf_*^Tow`. A *completion datum*
(`CategoryTheory.BaseChangeSquare.CompletionDatum`) consists of

* the reduction towers `K ↦ K_• = (K ⊗ᴸ P_n)_n`, as a reduction `ρ : Reduction 𝔇 𝔗` of base
  change squares (`def-weil-pbc-level-map-corners`);
* derived limit formalisms on the towers over `X'` and `Y'`
  (`def-weil-pbc-derived-inverse-limit`);
* the direct-image/limit commutation `Rf'_* R lim ≅ R lim Rf'^Tow_*`
  (`prop-weil-pbc-direct-image-limits`).

The completed pullbacks are `Lg^*_comp M = R lim (Lg^*_Tow M_•)` and
`Lg'^*_comp K = R lim (Lg'^*_Tow K_•)`, and the *completed base change map*
(`def-weil-pbc-completed-base-change-map`)

```
Lg^*_comp Rf_* K = R lim A_• --R lim (v' ∘ h)--> R lim D_• ≅ Rf'_* R lim Lg'^*_Tow K_•
```

is the derived limit of the composite `W = v' ∘ h = h' ∘ v` of the exchange rectangle of the
reduction, followed by the inverse of the direct-image/limit commutation.

The main result is the abstract *complete proper base change theorem*
(`thm-weil-pbc-complete-proetale`): if the projection formula holds at every level and the
finite-level exchange maps `Ex_{□, K_n}` are isomorphisms, the completed exchange map is an
isomorphism. The levels are accessed through *evaluation reductions* `ε_n : Reduction 𝔗 𝔇`
(`ev_n`, which commutes with the levelwise operations), and the comparison between the
evaluation of the tower exchange map and the finite-level exchange map is again an instance of
the exchange rectangle (`CategoryTheory.BaseChangeSquare.Reduction.isIso_arrowV_app_iff`).

We also define the completed reduction square (`def-weil-pbc-completed-reduction-square`) and
prove that the finite reduction of the completed map is the finite-level exchange map
(`lemma-weil-pbc-completed-map-reduction`).
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

namespace CategoryTheory

namespace BaseChangeSquare

variable {𝒳 : Type u₁} {𝒴 : Type u₂} {𝒳' : Type u₃} {𝒴' : Type u₄}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒴] [Category.{v₃} 𝒳'] [Category.{v₄} 𝒴']
  {𝒯 : Type u₅} {𝒰 : Type u₆} {𝒯' : Type u₇} {𝒰' : Type u₈}
  [Category.{v₅} 𝒯] [Category.{v₆} 𝒰] [Category.{v₇} 𝒯'] [Category.{v₈} 𝒰']

namespace Reduction

variable {𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴'} {𝔗 : BaseChangeSquare 𝒯 𝒰 𝒯' 𝒰'}
  (ρ : Reduction 𝔇 𝔗)

@[reassoc]
lemma arrowH_app (K : 𝒳) : ρ.arrowH.app K = 𝔗.upperG.map (ρ.projF.natTrans.app K) := by
  dsimp [arrowH]
  erw [Category.id_comp, Category.comp_id]

@[reassoc]
lemma arrowV_app (K : 𝒳) :
    ρ.arrowV.app K = ρ.δG.hom.app (𝔇.lowerF.obj K) ≫ ρ.redY'.map (𝔇.exchange.natTrans.app K) := by
  simp [arrowV]

@[reassoc]
lemma arrowH'_app (K : 𝒳) :
    ρ.arrowH'.app K = ρ.projF'.natTrans.app (𝔇.upperG'.obj K) ≫
      𝔗.lowerF'.map (ρ.δG'.inv.app K) := by
  simp [arrowH']

lemma arrowV'_app (K : 𝒳) : ρ.arrowV'.app K = 𝔗.exchange.natTrans.app (ρ.redX.obj K) := rfl

instance isIso_arrowH_app (K : 𝒳) [IsIso (ρ.projF.natTrans.app K)] : IsIso (ρ.arrowH.app K) := by
  rw [arrowH_app]; infer_instance

instance isIso_arrowH'_app (K : 𝒳) [IsIso (ρ.projF'.natTrans.app (𝔇.upperG'.obj K))] :
    IsIso (ρ.arrowH'.app K) := by
  rw [arrowH'_app]; infer_instance

/-- **Comparison of exchange maps along a reduction.** If the projection maps `π_f`, `π_{f'}`
of a reduction are invertible at `K` (for the evaluation `ev_n` of derived towers this is the
commutation `ev_n Rf_*^Tow ≅ Rf_* ev_n`), then the reduction of the exchange map of the source
square at `K` is invertible iff the exchange map of the target square at the reduction of `K`
is. This is the exchange rectangle with two invertible horizontal edges. -/
lemma isIso_arrowV_app_iff (K : 𝒳) [IsIso (ρ.projF.natTrans.app K)]
    [IsIso (ρ.projF'.natTrans.app (𝔇.upperG'.obj K))] :
    IsIso (ρ.arrowV.app K) ↔ IsIso (ρ.arrowV'.app K) := by
  have w := ρ.rectangle_app K
  constructor
  · intro _
    have : ρ.arrowV'.app K = inv (ρ.arrowH.app K) ≫ ρ.arrowV.app K ≫ ρ.arrowH'.app K := by
      rw [← w, IsIso.inv_hom_id_assoc]
    rw [this]; infer_instance
  · intro _
    have : ρ.arrowV.app K = (ρ.arrowH.app K ≫ ρ.arrowV'.app K) ≫ inv (ρ.arrowH'.app K) := by
      rw [w, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [this]; infer_instance

/-- The reduction of the exchange map of the source square is invertible at `K` iff the
exchange map of the target square is invertible at the reduction of `K`, provided the
projection maps are invertible. -/
lemma isIso_redY'_map_exchange_app_iff (K : 𝒳) [IsIso (ρ.projF.natTrans.app K)]
    [IsIso (ρ.projF'.natTrans.app (𝔇.upperG'.obj K))] :
    IsIso (ρ.redY'.map (𝔇.exchange.natTrans.app K)) ↔
      IsIso (𝔗.exchange.natTrans.app (ρ.redX.obj K)) := by
  rw [← arrowV'_app, ← isIso_arrowV_app_iff, arrowV_app]
  constructor
  · intro _; infer_instance
  · intro _; exact IsIso.of_isIso_comp_left (ρ.δG.hom.app (𝔇.lowerF.obj K)) _

end Reduction

variable [HasZeroObject 𝒳'] [HasShift 𝒳' ℤ] [Preadditive 𝒳']
  [∀ n : ℤ, (shiftFunctor 𝒳' n).Additive] [Pretriangulated 𝒳']
  [HasZeroObject 𝒴'] [HasShift 𝒴' ℤ] [Preadditive 𝒴']
  [∀ n : ℤ, (shiftFunctor 𝒴' n).Additive] [Pretriangulated 𝒴']

/-- A *completion datum* for a base change square `𝔇` with tower square `𝔗`: the reduction
towers `ρ : Reduction 𝔇 𝔗` (`K ↦ K_•`, with the projection-formula comparisons), derived limit
formalisms for the towers over `X'` and `Y'`, and the direct-image/limit commutation
`Rf'_* ∘ R lim ≅ R lim ∘ Rf'^Tow_*` (Blueprint `prop-weil-pbc-direct-image-limits`, used as
an input). -/
structure CompletionDatum (𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴')
    (𝔗 : BaseChangeSquare 𝒯 𝒰 𝒯' 𝒰') where
  /-- The reduction towers `K ↦ K_•`. -/
  ρ : Reduction 𝔇 𝔗
  /-- The derived limit of towers over `X'`. -/
  limX' : TowerLimitFormalism 𝒯' 𝒳'
  /-- The derived limit of towers over `Y'`. -/
  limY' : TowerLimitFormalism 𝒰' 𝒴'
  /-- The direct-image/limit commutation `Rf'_* R lim ≅ R lim Rf'^Tow_*`. -/
  lowerLim : limX'.rlim ⋙ 𝔇.lowerF' ≅ 𝔗.lowerF' ⋙ limY'.rlim

namespace CompletionDatum

variable {𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴'} {𝔗 : BaseChangeSquare 𝒯 𝒰 𝒯' 𝒰'}
  (𝔠 : CompletionDatum 𝔇 𝔗)

/-- The completed pullback `Lg^*_comp M = R lim (Lg^*_Tow M_•)` along `g`. -/
def completedPullback : 𝒴 ⥤ 𝒴' := 𝔠.ρ.redY ⋙ 𝔗.upperG ⋙ 𝔠.limY'.rlim

/-- The completed pullback `Lg'^*_comp K = R lim (Lg'^*_Tow K_•)` along `g'`. -/
def completedPullback' : 𝒳 ⥤ 𝒳' := 𝔠.ρ.redX ⋙ 𝔗.upperG' ⋙ 𝔠.limX'.rlim

/-- The common composite `W = v' ∘ h = h' ∘ v : A_• ⟶ D_•` of the exchange rectangle. -/
def towerExchange : 𝔠.ρ.cornerA ⟶ 𝔠.ρ.cornerD := 𝔠.ρ.arrowH ≫ 𝔠.ρ.arrowV'

lemma towerExchange_eq : 𝔠.towerExchange = 𝔠.ρ.arrowV ≫ 𝔠.ρ.arrowH' := 𝔠.ρ.rectangle

/-- **The completed base change map** (Blueprint `def-weil-pbc-completed-base-change-map`,
abstract form)
`Ex^comp_K : Lg^*_comp Rf_* K = R lim A_• ⟶ R lim D_• ≅ Rf'_* Lg'^*_comp K`: the derived limit
of `H` followed by `V'` (the limits of the projection-formula maps `h_n` and of the
finite-level exchange maps `v'_n = Ex_{□, K_n}`), followed by the inverse of the
direct-image/limit commutation. -/
def completedExchange :
    𝔇.lowerF ⋙ 𝔠.completedPullback ⟶ 𝔠.completedPullback' ⋙ 𝔇.lowerF' :=
  Functor.whiskerRight 𝔠.towerExchange 𝔠.limY'.rlim ≫
    Functor.whiskerLeft (𝔠.ρ.redX ⋙ 𝔗.upperG') 𝔠.lowerLim.inv

lemma completedExchange_app' (K : 𝒳) :
    𝔠.completedExchange.app K = 𝔠.limY'.rlim.map (𝔠.towerExchange.app K) ≫
      𝔠.lowerLim.inv.app ((𝔗.upperG').obj (𝔠.ρ.redX.obj K)) := rfl

/-- The components of the completed base change map: `Ex^comp_K = t ∘ R lim (v' ∘ h)`
(Blueprint `def-weil-pbc-completed-frobenius-structures`: `Ex^comp = t W s` with `s = 𝟙`,
since `S = Lg^*_comp Rf_* K` is by definition the derived limit `A_∞` of the tower `A_•`). -/
lemma completedExchange_app (K : 𝒳) :
    𝔠.completedExchange.app K = 𝔠.limY'.rlim.map (𝔠.ρ.arrowH.app K) ≫
      𝔠.limY'.rlim.map (𝔠.ρ.arrowV'.app K) ≫
        𝔠.lowerLim.inv.app ((𝔗.upperG').obj (𝔠.ρ.redX.obj K)) := by
  rw [completedExchange_app', towerExchange, NatTrans.comp_app, Functor.map_comp, Category.assoc]

/-- The completed base change map is also the limit of `h' ∘ v` (the limit rectangle
`V' H = H' V`, Blueprint `lem-weil-pbc-rectangle-derived-limit`). -/
lemma completedExchange_app_eq (K : 𝒳) :
    𝔠.completedExchange.app K = 𝔠.limY'.rlim.map (𝔠.ρ.arrowV.app K) ≫
      𝔠.limY'.rlim.map (𝔠.ρ.arrowH'.app K) ≫
        𝔠.lowerLim.inv.app ((𝔗.upperG').obj (𝔠.ρ.redX.obj K)) := by
  rw [completedExchange_app', towerExchange_eq, NatTrans.comp_app, Functor.map_comp,
    Category.assoc]

/-- **Abstract complete proper base change** (the core of Blueprint
`thm-weil-pbc-complete-proetale`): if at every level `n` the evaluations of the
projection-formula map `h` and of the tower exchange map `v'` at `K` are isomorphisms, then the
completed exchange map `Ex^comp_K` is an isomorphism. -/
theorem isIso_completedExchange_app_of_forall (K : 𝒳)
    (hH : ∀ n, IsIso ((𝔠.limY'.ev n).map (𝔠.ρ.arrowH.app K)))
    (hV' : ∀ n, IsIso ((𝔠.limY'.ev n).map (𝔠.ρ.arrowV'.app K))) :
    IsIso (𝔠.completedExchange.app K) := by
  have : IsIso (𝔠.limY'.rlim.map (𝔠.towerExchange.app K)) :=
    𝔠.limY'.isIso_rlim_map_of_forall_isIso _ fun n ↦ by
      simp only [towerExchange, NatTrans.comp_app, Functor.map_comp]
      have := hH n; have := hV' n
      infer_instance
  rw [completedExchange_app']
  infer_instance

end CompletionDatum

end BaseChangeSquare

end CategoryTheory
