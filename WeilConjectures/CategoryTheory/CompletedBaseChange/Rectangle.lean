/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The exchange rectangle of a reduction of base change squares

A *base change square* is a square of categories

```
  𝒳  --g'^*-->  𝒳'
  ↑ f^*          ↑ f'^*
  𝒴  --g^*--->  𝒴'
```

with adjunctions `f^* ⊣ f_*`, `f'^* ⊣ f'_*` and an isomorphism `β : g^* ⋙ f'^* ≅ f^* ⋙ g'^*`
(the Cartesian identification). Its *exchange map* `ξ : f_* ⋙ g^* ⟶ g'^* ⋙ f'_*` is the mate of
`β`. This is the abstract shape of the proper base change situation `Lg^* Rf_* ⟶ Rf'_* Lg'^*`.

A *reduction* of a base change square `𝔇` into a second one `𝔗` consists of functors
`red_Z : 𝔇_Z ⥤ 𝔗_Z` on the four corners, together with comparison 2-squares
`γ_f : red_Y ⋙ F^* ⟶ f^* ⋙ red_X`, `γ_{f'}` and isomorphisms
`δ_g : red_Y ⋙ G^* ≅ g^* ⋙ red_{Y'}`, `δ_{g'}`, which make the cube of left adjoints commute.
The intended example is the reduction `K ↦ K ⊗ᴸ P_n` modulo `Iⁿ` (one `n` at a time, with
`𝔗 = 𝔇`), or the reduction tower `K ↦ K_•` into derived categories of towers. The mate
`π_f : f_* ⋙ red_Y ⟶ red_X ⋙ F_*` of `γ_f` is then the projection-formula map
`(Rf_* K) ⊗ᴸ P ⟶ Rf_*(K ⊗ᴸ Lf^* P)`.

For `K` on `𝒳`, the four *corners* (`def-weil-pbc-level-map-corners`,
`def-weil-pbc-four-corners`) are

```
  A = G^* red_Y f_* K,     B = G^* F_* red_X K,
  C = red_{Y'} f'_* g'^* K, D = F'_* G'^* red_X K,
```

and the four *arrows* (`def-weil-pbc-level-map-arrows`, `def-weil-pbc-four-arrows`) are
`h = G^* π_f`, `v = red_{Y'} ξ ∘ δ_g`, `h' = δ_{g'}⁻¹ ∘ π_{f'}` and `v' = ξ^𝔗 red_X`.
The *exchange rectangle* `v' ∘ h = h' ∘ v` (`lemma-weil-pbc-level-map-rectangle`,
`lem-weil-pbc-finite-level-rectangle`) is proved by identifying both composites with mates of
the two halves of the cube, which agree by the cube condition.

## Main definitions

- `CategoryTheory.BaseChangeSquare`, `CategoryTheory.BaseChangeSquare.exchange`.
- `CategoryTheory.BaseChangeSquare.Reduction`, with the projection maps `projF`, `projF'`,
  the corners `cornerA` … `cornerD` and arrows `arrowH`, `arrowV`, `arrowH'`, `arrowV'`.

## Main results

- `CategoryTheory.BaseChangeSquare.Reduction.rectangle`: `h ≫ v' = v ≫ h'`.
- `CategoryTheory.BaseChangeSquare.Reduction.rectangle_app_naturality`: the rectangle is
  natural in `K`, i.e. all four arrows commute with the operators induced by an endomorphism of
  `K` (`lemma-weil-pbc-level-map-operator-naturality`).
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open CategoryTheory CategoryTheory.Functor CategoryTheory.TwoSquare

namespace CategoryTheory

/-- A *base change square*: categories `𝒳, 𝒴, 𝒳', 𝒴'`, left adjoints `f^* : 𝒴 ⥤ 𝒳`,
`f'^* : 𝒴' ⥤ 𝒳'` with right adjoints `f_*`, `f'_*`, pullbacks `g^* : 𝒴 ⥤ 𝒴'`,
`g'^* : 𝒳 ⥤ 𝒳'` and the Cartesian identification `β : g^* ⋙ f'^* ≅ f^* ⋙ g'^*`.

This is the abstract shape of `def-weil-pbc-cartesian-square` on derived categories. -/
structure BaseChangeSquare (𝒳 : Type u₁) (𝒴 : Type u₂) (𝒳' : Type u₃) (𝒴' : Type u₄)
    [Category.{v₁} 𝒳] [Category.{v₂} 𝒴] [Category.{v₃} 𝒳'] [Category.{v₄} 𝒴'] where
  /-- The pullback `f^*`. -/
  upperF : 𝒴 ⥤ 𝒳
  /-- The direct image `f_*`. -/
  lowerF : 𝒳 ⥤ 𝒴
  /-- The adjunction `f^* ⊣ f_*`. -/
  adjF : upperF ⊣ lowerF
  /-- The pullback `f'^*`. -/
  upperF' : 𝒴' ⥤ 𝒳'
  /-- The direct image `f'_*`. -/
  lowerF' : 𝒳' ⥤ 𝒴'
  /-- The adjunction `f'^* ⊣ f'_*`. -/
  adjF' : upperF' ⊣ lowerF'
  /-- The pullback `g^*`. -/
  upperG : 𝒴 ⥤ 𝒴'
  /-- The pullback `g'^*`. -/
  upperG' : 𝒳 ⥤ 𝒳'
  /-- The Cartesian identification `g^* ⋙ f'^* ≅ f^* ⋙ g'^*`. -/
  iso : upperG ⋙ upperF' ≅ upperF ⋙ upperG'

namespace BaseChangeSquare

variable {𝒳 : Type u₁} {𝒴 : Type u₂} {𝒳' : Type u₃} {𝒴' : Type u₄}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒴] [Category.{v₃} 𝒳'] [Category.{v₄} 𝒴']

/-- The Cartesian identification as a 2-square, the input of the mate calculus. -/
abbrev isoSquare (𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴') :
    TwoSquare 𝔇.upperG 𝔇.upperF 𝔇.upperF' 𝔇.upperG' :=
  TwoSquare.mk _ _ _ _ 𝔇.iso.hom

/-- The *exchange map* `ξ : f_* ⋙ g^* ⟶ g'^* ⋙ f'_*` of a base change square, the mate of the
Cartesian identification with respect to `f^* ⊣ f_*` and `f'^* ⊣ f'_*`; it is the unit–counit
composite `g^* f_* ⟶ f'_* f'^* g^* f_* ≅ f'_* g'^* f^* f_* ⟶ f'_* g'^*`. -/
def exchange (𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴') :
    TwoSquare 𝔇.lowerF 𝔇.upperG' 𝔇.upperG 𝔇.lowerF' :=
  mateEquiv 𝔇.adjF 𝔇.adjF' 𝔇.isoSquare

variable {𝒯 : Type u₅} {𝒰 : Type u₆} {𝒯' : Type u₇} {𝒰' : Type u₈}
  [Category.{v₅} 𝒯] [Category.{v₆} 𝒰] [Category.{v₇} 𝒯'] [Category.{v₈} 𝒰']

/-- A *reduction* of a base change square `𝔇` into a base change square `𝔗`: functors
`red_Z` on the four corners, comparison 2-squares `γ_f : red_Y ⋙ F^* ⟶ f^* ⋙ red_X` and
`γ_{f'}` for the two adjunction sides, and isomorphisms `δ_g : red_Y ⋙ G^* ≅ g^* ⋙ red_{Y'}`,
`δ_{g'}` for the two pullback sides, such that the cube of left adjoints commutes: the two
composite 2-squares `red_Y ⋙ G^* ⋙ F'^* ⟶ f^* ⋙ red_X ⋙ G'^*` agree.

For the reduction modulo `Iⁿ`, `red_Z = - ⊗ᴸ P_n` and the comparisons are the monoidal
structure isomorphisms of the pullbacks. -/
structure Reduction (𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴') (𝔗 : BaseChangeSquare 𝒯 𝒰 𝒯' 𝒰') where
  /-- The reduction on `𝒳`. -/
  redX : 𝒳 ⥤ 𝒯
  /-- The reduction on `𝒴`. -/
  redY : 𝒴 ⥤ 𝒰
  /-- The reduction on `𝒳'`. -/
  redX' : 𝒳' ⥤ 𝒯'
  /-- The reduction on `𝒴'`. -/
  redY' : 𝒴' ⥤ 𝒰'
  /-- The comparison `red_Y ⋙ F^* ⟶ f^* ⋙ red_X`. -/
  γF : TwoSquare redY 𝔇.upperF 𝔗.upperF redX
  /-- The comparison `red_{Y'} ⋙ F'^* ⟶ f'^* ⋙ red_{X'}`. -/
  γF' : TwoSquare redY' 𝔇.upperF' 𝔗.upperF' redX'
  /-- The comparison `red_Y ⋙ G^* ≅ g^* ⋙ red_{Y'}`. -/
  δG : redY ⋙ 𝔗.upperG ≅ 𝔇.upperG ⋙ redY'
  /-- The comparison `red_X ⋙ G'^* ≅ g'^* ⋙ red_{X'}`. -/
  δG' : redX ⋙ 𝔗.upperG' ≅ 𝔇.upperG' ⋙ redX'
  /-- The cube of left adjoints commutes. -/
  cube : γF ≫ₕ 𝔗.isoSquare =
    ((𝔇.isoSquare ≫ₕ γF').whiskerTop δG.hom).whiskerBottom δG'.inv

namespace Reduction

variable {𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴'} {𝔗 : BaseChangeSquare 𝒯 𝒰 𝒯' 𝒰'}
  (ρ : Reduction 𝔇 𝔗)

/-- The projection map `π_f : f_* ⋙ red_Y ⟶ red_X ⋙ F_*`, the mate of `γ_f`
(`def-weil-pbc-projection-formula-map` in the abstract). -/
def projF : TwoSquare 𝔇.lowerF ρ.redX ρ.redY 𝔗.lowerF :=
  mateEquiv 𝔇.adjF 𝔗.adjF ρ.γF

/-- The projection map `π_{f'} : f'_* ⋙ red_{Y'} ⟶ red_{X'} ⋙ F'_*`, the mate of `γ_{f'}`. -/
def projF' : TwoSquare 𝔇.lowerF' ρ.redX' ρ.redY' 𝔗.lowerF' :=
  mateEquiv 𝔇.adjF' 𝔗.adjF' ρ.γF'

/-- The corner `A = G^* (red_Y (f_* K))` (Blueprint `def-weil-pbc-level-map-corners`,
`def-weil-pbc-four-corners`: `A_n = Lg^*((Rf_* K) ⊗ᴸ P_n)`). -/
def cornerA : 𝒳 ⥤ 𝒰' := 𝔇.lowerF ⋙ ρ.redY ⋙ 𝔗.upperG

/-- The corner `B = G^* (F_* (red_X K))` (`B_n = Lg^* Rf_* K_n`). -/
def cornerB : 𝒳 ⥤ 𝒰' := ρ.redX ⋙ 𝔗.lowerF ⋙ 𝔗.upperG

/-- The corner `C = red_{Y'} (f'_* (g'^* K))` (`C_n = (Rf'_* E) ⊗ᴸ P_n`). -/
def cornerC : 𝒳 ⥤ 𝒰' := 𝔇.upperG' ⋙ 𝔇.lowerF' ⋙ ρ.redY'

/-- The corner `D = F'_* (G'^* (red_X K))` (`D_n = Rf'_* E_n`). -/
def cornerD : 𝒳 ⥤ 𝒰' := ρ.redX ⋙ 𝔗.upperG' ⋙ 𝔗.lowerF'

/-- The arrow `h = G^* π_f : A ⟶ B` (Blueprint `def-weil-pbc-level-map-arrows`,
`def-weil-pbc-four-arrows`). -/
def arrowH : ρ.cornerA ⟶ ρ.cornerB :=
  (associator _ _ _).inv ≫ whiskerRight ρ.projF.natTrans 𝔗.upperG ≫ (associator _ _ _).hom

/-- The arrow `v = red_{Y'} ξ ∘ δ_g : A ⟶ C`, the reduction of the exchange map transported
through `G^* red_Y ≅ red_{Y'} g^*`. -/
def arrowV : ρ.cornerA ⟶ ρ.cornerC :=
  whiskerLeft 𝔇.lowerF ρ.δG.hom ≫ (associator _ _ _).inv ≫
    whiskerRight 𝔇.exchange.natTrans ρ.redY' ≫ (associator _ _ _).hom

/-- The arrow `h' = F'_* δ_{g'}⁻¹ ∘ π_{f'} : C ⟶ D`. -/
def arrowH' : ρ.cornerC ⟶ ρ.cornerD :=
  whiskerLeft 𝔇.upperG' ρ.projF'.natTrans ≫ (associator _ _ _).inv ≫
    whiskerRight ρ.δG'.inv 𝔗.lowerF' ≫ (associator _ _ _).hom

/-- The arrow `v' = ξ^𝔗 red_X : B ⟶ D`, the exchange map of `𝔗` at the reduction of `K`. -/
def arrowV' : ρ.cornerB ⟶ ρ.cornerD :=
  whiskerLeft ρ.redX 𝔗.exchange.natTrans

/-- The composite `h ≫ v'` is the mate of the upper half `γ_f ≫ₕ β^𝔗` of the cube. -/
lemma arrowH_comp_arrowV' :
    ρ.arrowH ≫ ρ.arrowV' =
      (mateEquiv 𝔇.adjF 𝔗.adjF' (ρ.γF ≫ₕ 𝔗.isoSquare)).natTrans := by
  rw [mateEquiv_vcomp 𝔇.adjF 𝔗.adjF 𝔗.adjF']
  ext K
  simp [arrowH, arrowV', projF, exchange, cornerA, cornerB, cornerD, TwoSquare.vComp]

/-- The composite `v ≫ h'` is the mate of the lower half of the cube, whiskered by `δ_g` and
`δ_{g'}⁻¹`. -/
lemma arrowV_comp_arrowH' :
    ρ.arrowV ≫ ρ.arrowH' = (mateEquiv 𝔇.adjF 𝔗.adjF'
      (((𝔇.isoSquare ≫ₕ ρ.γF').whiskerTop ρ.δG.hom).whiskerBottom ρ.δG'.inv)).natTrans := by
  rw [mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp 𝔇.adjF 𝔇.adjF' 𝔗.adjF']
  ext K
  simp [arrowV, arrowH', projF', exchange, cornerA, cornerC, cornerD, TwoSquare.vComp,
    TwoSquare.whiskerLeft, TwoSquare.whiskerRight]

/-- **The exchange rectangle** (Blueprint `lemma-weil-pbc-level-map-rectangle`,
`lem-weil-pbc-finite-level-rectangle`, abstract form): `v' ∘ h = h' ∘ v : A ⟶ D`.
Both composites are mates of the two halves of the commutative cube of left adjoints. -/
theorem rectangle : ρ.arrowH ≫ ρ.arrowV' = ρ.arrowV ≫ ρ.arrowH' := by
  rw [arrowH_comp_arrowV', arrowV_comp_arrowH', ρ.cube]

@[reassoc]
lemma rectangle_app (K : 𝒳) :
    ρ.arrowH.app K ≫ ρ.arrowV'.app K = ρ.arrowV.app K ≫ ρ.arrowH'.app K := by
  rw [← NatTrans.comp_app, ρ.rectangle, NatTrans.comp_app]

/-- **Operator naturality of the rectangle** (Blueprint
`lemma-weil-pbc-level-map-operator-naturality`, abstract form): for an endomorphism (or any
morphism) `φ : K ⟶ K'`, the four arrows intertwine the induced maps on the corners, and the
common composite `v' ∘ h = h' ∘ v` is natural. -/
lemma rectangle_app_naturality {K K' : 𝒳} (φ : K ⟶ K') :
    ρ.cornerA.map φ ≫ ρ.arrowH.app K' = ρ.arrowH.app K ≫ ρ.cornerB.map φ ∧
    ρ.cornerA.map φ ≫ ρ.arrowV.app K' = ρ.arrowV.app K ≫ ρ.cornerC.map φ ∧
    ρ.cornerC.map φ ≫ ρ.arrowH'.app K' = ρ.arrowH'.app K ≫ ρ.cornerD.map φ ∧
    ρ.cornerB.map φ ≫ ρ.arrowV'.app K' = ρ.arrowV'.app K ≫ ρ.cornerD.map φ ∧
    ρ.cornerA.map φ ≫ ρ.arrowH.app K' ≫ ρ.arrowV'.app K' =
      (ρ.arrowV.app K ≫ ρ.arrowH'.app K) ≫ ρ.cornerD.map φ :=
  ⟨(ρ.arrowH.naturality φ), (ρ.arrowV.naturality φ), (ρ.arrowH'.naturality φ),
    (ρ.arrowV'.naturality φ), by
      rw [← ρ.rectangle_app, Category.assoc, ← ρ.arrowV'.naturality,
        ← Category.assoc, ρ.arrowH.naturality, Category.assoc]⟩

end Reduction

end BaseChangeSquare

end CategoryTheory
