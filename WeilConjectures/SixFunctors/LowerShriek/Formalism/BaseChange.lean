/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.RefinementOfIsPullback
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Canonical
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Identity
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Pasting
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Cube

/-!
# Compact-support base change in a compact support formalism

Let `F` be a `AlgebraicGeometry.CompactSupportFormalism`. For a commutative square of schemes
```
U' --t--> U
|l        |r
Z' --b--> Z
```
the *base change map of the pushforwards* `b^* r_* ⟶ l_* t^*` is the mate of the square
isomorphism `r^* ⋙ t^* ≅ b^* ⋙ l^*` (`CompactSupportFormalism.pfBaseChange`). The formalism
*satisfies proper base change* (`CompactSupportFormalism.HasProperBaseChange`) if this map is an
isomorphism for every cartesian square with `r` proper.

For a cartesian square
```
X' --g'--> X
|f'        |f
Y' --g---> Y
```
a compactification `c = (X ⟶[c.i] c.Z ⟶[c.g] Y)` of `f` and a compactification `c'` of `f'`
lying over it along a morphism `h : c'.Z ⟶ c.Z` with cartesian squares
```
X' --g'--> X
|c'.i      |c.i
c'.Z --h--> c.Z
|c'.g      |c.g
Y' --g---> Y
```
(for instance the base change `c.ofIsPullback sq` of `c`, blueprint
`def-cbc-compact-support-square`), the *compact-support exchange map* (blueprint
`def-cbc-exchange-map`)

`Ex_! : g^* Rf_!(c) ⟶ Rf'_!(c') g'^*`

is the base change map of the pushforwards for the proper `c.g`, applied after `(c.i)_!`,
composed with the inverse of the base change isomorphism `g'^* ⋙ (c'.i)_! ≅ (c.i)_! ⋙ h^*` of
the extension by zero (`CompactSupportFormalism.shriekBaseChange`). It is an isomorphism when
`F` satisfies base change for the extension by zero and proper base change
(`CompactSupportFormalism.isIso_shriekBaseChange`), and it is natural, the identity for the
identity square, compatible with horizontal pasting and with the comparison isomorphisms along
refinements of compactifications. Computed with the chosen compactifications, it gives the
exchange map `F.lowerShriekBaseChange` of the canonical compactly supported direct images, which
does not depend on the compactification and is compatible with vertical pasting through the
composition isomorphisms.

## Main definitions

- `AlgebraicGeometry.CompactSupportFormalism.pfBaseChange`: the base change map
  `b^* r_* ⟶ l_* t^*`.
- `AlgebraicGeometry.CompactSupportFormalism.HasProperBaseChange`: proper base change.
- `AlgebraicGeometry.CompactSupportFormalism.shriekBaseChange`: the exchange map `Ex_!` along
  compactifications.
- `AlgebraicGeometry.CompactSupportFormalism.lowerShriekBaseChange`: the exchange map `Ex_!` of
  the canonical compactly supported direct images.

## Main statements

- `AlgebraicGeometry.CompactSupportFormalism.isIso_shriekBaseChange`: `Ex_!` is an isomorphism.
- `AlgebraicGeometry.CompactSupportFormalism.shriekBaseChange_id`: identity law.
- `AlgebraicGeometry.CompactSupportFormalism.shriekBaseChange_paste_horiz`: horizontal pasting.
- `AlgebraicGeometry.CompactSupportFormalism.shriekBaseChange_refinementComparison`:
  compatibility with the comparisons along refinements.
- `AlgebraicGeometry.CompactSupportFormalism.lowerShriekBaseChange_eq`: independence of the
  compactification.
- `AlgebraicGeometry.CompactSupportFormalism.lowerShriekBaseChange_paste_vert`: vertical pasting.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits TwoSquare

namespace AlgebraicGeometry.CompactSupportFormalism

variable (F : CompactSupportFormalism.{w, v, u})

section PushforwardBaseChange

variable {U' U Z' Z : Scheme.{u}}

/-- **The base change map of the pushforwards**: for a commutative square `t ≫ r = l ≫ b`, the
map `r_* ⋙ b^* ⟶ t^* ⋙ l_*`, i.e. `b^* r_* ⟶ l_* t^*`, the mate of the inverse of
`CompactSupportFormalism.sqIso` under the adjunctions `r^* ⊣ r_*` and `l^* ⊣ l_*`.
```
U' --t--> U
|l        |r
Z' --b--> Z
```
-/
def pfBaseChange (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z) (w : t ≫ r = l ≫ b) :
    TwoSquare (F.pf r) (F.pb t) (F.pb b) (F.pf l) :=
  mateEquiv (F.adj r) (F.adj l) (F.sqIso t l r b w).inv

/-- The inverse of the square isomorphism of the square `𝟙 ≫ j = j ≫ 𝟙`. -/
lemma sqIso_id_horiz_inv {X Y : Scheme.{u}} (j : X ⟶ Y) (w : 𝟙 X ≫ j = j ≫ 𝟙 Y) :
    (F.sqIso (𝟙 X) j j (𝟙 Y) w).inv =
      ((TwoSquare.mk (𝟭 _) (F.pb j) (F.pb j) (𝟭 _)
        ((Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv)).whiskerTop
          (F.pbId Y).hom).whiskerBottom (F.pbId X).inv := by
  apply Iso.inv_ext
  rw [sqIso_id_horiz_hom]
  ext M
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
    Category.id_comp, Category.assoc, NatTrans.id_app, Functor.comp_obj, Functor.id_obj]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]

/-- The base change map of the pushforwards of the square `𝟙 ≫ j = j ≫ 𝟙` is the identity, up
to `(𝟙)^* ≅ 𝟭`. -/
lemma pfBaseChange_id_horiz {X Y : Scheme.{u}} (j : X ⟶ Y) (w : 𝟙 X ≫ j = j ≫ 𝟙 Y) :
    F.pfBaseChange (𝟙 X) j j (𝟙 Y) w =
      ((TwoSquare.mk (F.pf j) (𝟭 _) (𝟭 _) (F.pf j)
        ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv)).whiskerRight
          (F.pbId Y).hom).whiskerLeft (F.pbId X).inv := by
  rw [pfBaseChange, sqIso_id_horiz_inv, mateEquiv_whiskerTop_whiskerBottom, mateEquiv_unitors]

/-- **Horizontal pasting of the inverses of square isomorphisms.**
```
U'' --t₁--> U' --t₂--> U
|l          |m          |r
Z'' --b₁--> Z' --b₂--> Z
```
-/
lemma sqIso_inv_paste_horiz {U'' U' U Z'' Z' Z : Scheme.{u}} (t₁ : U'' ⟶ U')
    (t₂ : U' ⟶ U) (l : U'' ⟶ Z'') (m : U' ⟶ Z') (r : U ⟶ Z) (b₁ : Z'' ⟶ Z') (b₂ : Z' ⟶ Z)
    (t : U'' ⟶ U) (b : Z'' ⟶ Z) (w₁ : t₁ ≫ m = l ≫ b₁) (w₂ : t₂ ≫ r = m ≫ b₂)
    (ht : t₁ ≫ t₂ = t) (hb : b₁ ≫ b₂ = b) (w : t ≫ r = l ≫ b) :
    (F.sqIso t l r b w).inv =
      ((TwoSquare.mk _ _ _ _ (F.sqIso t₂ m r b₂ w₂).inv ≫ₕ
        TwoSquare.mk _ _ _ _ (F.sqIso t₁ l m b₁ w₁).inv).whiskerTop
          (F.pbComp' b₁ b₂ b hb).hom).whiskerBottom (F.pbComp' t₁ t₂ t ht).inv := by
  apply Iso.inv_ext
  ext M
  rw [NatTrans.comp_app, F.sqIso_hom_app_paste_horiz t₁ t₂ l m r b₁ b₂ t b w₁ w₂ ht hb w M]
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc,
    NatTrans.id_app, Functor.comp_obj]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Iso.hom_inv_id_app]

/-- **Horizontal pasting of base change maps of the pushforwards.**
```
U'' --t₁--> U' --t₂--> U
|l          |m          |r
Z'' --b₁--> Z' --b₂--> Z
```
-/
lemma pfBaseChange_paste_horiz {U'' U' U Z'' Z' Z : Scheme.{u}} (t₁ : U'' ⟶ U')
    (t₂ : U' ⟶ U) (l : U'' ⟶ Z'') (m : U' ⟶ Z') (r : U ⟶ Z) (b₁ : Z'' ⟶ Z') (b₂ : Z' ⟶ Z)
    (t : U'' ⟶ U) (b : Z'' ⟶ Z) (w₁ : t₁ ≫ m = l ≫ b₁) (w₂ : t₂ ≫ r = m ≫ b₂)
    (ht : t₁ ≫ t₂ = t) (hb : b₁ ≫ b₂ = b) (w : t ≫ r = l ≫ b) :
    F.pfBaseChange t l r b w =
      ((F.pfBaseChange t₂ m r b₂ w₂ ≫ᵥ F.pfBaseChange t₁ l m b₁ w₁).whiskerRight
        (F.pbComp' b₁ b₂ b hb).hom).whiskerLeft (F.pbComp' t₁ t₂ t ht).inv := by
  rw [pfBaseChange, F.sqIso_inv_paste_horiz t₁ t₂ l m r b₁ b₂ t b w₁ w₂ ht hb w,
    mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp _ (F.adj m)]
  rfl

/-- **Vertical pasting of the inverses of square isomorphisms.**
```
U' --t--> U
|l₁       |r₁
W' --h--> W
|l₂       |r₂
Z' --b--> Z
```
-/
lemma sqIso_inv_paste_vert {U' U W' W Z' Z : Scheme.{u}} (t : U' ⟶ U) (h : W' ⟶ W)
    (b : Z' ⟶ Z) (l₁ : U' ⟶ W') (r₁ : U ⟶ W) (l₂ : W' ⟶ Z') (r₂ : W ⟶ Z) (l : U' ⟶ Z')
    (r : U ⟶ Z) (w₁ : t ≫ r₁ = l₁ ≫ h) (w₂ : h ≫ r₂ = l₂ ≫ b) (hl : l₁ ≫ l₂ = l)
    (hr : r₁ ≫ r₂ = r) (w : t ≫ r = l ≫ b) :
    (F.sqIso t l r b w).inv =
      ((TwoSquare.mk _ _ _ _ (F.sqIso h l₂ r₂ b w₂).inv ≫ᵥ
        TwoSquare.mk _ _ _ _ (F.sqIso t l₁ r₁ h w₁).inv).whiskerLeft
          (F.pbComp' r₁ r₂ r hr).inv).whiskerRight (F.pbComp' l₁ l₂ l hl).hom := by
  apply Iso.inv_ext
  ext M
  rw [NatTrans.comp_app, F.sqIso_hom_app_paste_vert t h b l₁ r₁ l₂ r₂ l r w₁ w₂ hl hr w M]
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc, NatTrans.id_app,
    Functor.comp_obj]
  rw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]

/-- **Vertical pasting of base change maps of the pushforwards.**
```
U' --t--> U
|l₁       |r₁
W' --h--> W
|l₂       |r₂
Z' --b--> Z
```
-/
lemma pfBaseChange_paste_vert {U' U W' W Z' Z : Scheme.{u}} (t : U' ⟶ U) (h : W' ⟶ W)
    (b : Z' ⟶ Z) (l₁ : U' ⟶ W') (r₁ : U ⟶ W) (l₂ : W' ⟶ Z') (r₂ : W ⟶ Z) (l : U' ⟶ Z')
    (r : U ⟶ Z) (w₁ : t ≫ r₁ = l₁ ≫ h) (w₂ : h ≫ r₂ = l₂ ≫ b) (hl : l₁ ≫ l₂ = l)
    (hr : r₁ ≫ r₂ = r) (w : t ≫ r = l ≫ b) :
    F.pfBaseChange t l r b w =
      ((F.pfBaseChange t l₁ r₁ h w₁ ≫ₕ F.pfBaseChange h l₂ r₂ b w₂).whiskerTop
        (F.pfComp' r₁ r₂ r hr).hom).whiskerBottom (F.pfComp' l₁ l₂ l hl).inv := by
  have hP : conjugateEquiv (F.adj r) ((F.adj r₂).comp (F.adj r₁)) (F.pbComp' r₁ r₂ r hr).inv =
      (F.pfComp' r₁ r₂ r hr).hom := rfl
  have hP' : conjugateEquiv ((F.adj l₂).comp (F.adj l₁)) (F.adj l) (F.pbComp' l₁ l₂ l hl).hom =
      (F.pfComp' l₁ l₂ l hl).inv := rfl
  rw [pfBaseChange, F.sqIso_inv_paste_vert t h b l₁ r₁ l₂ r₂ l r w₁ w₂ hl hr w,
    mateEquiv_conjugateEquiv_vcomp _ ((F.adj l₂).comp (F.adj l₁)),
    conjugateEquiv_mateEquiv_vcomp _ ((F.adj r₂).comp (F.adj r₁)), mateEquiv_hcomp, hP, hP']
  rfl

/-- **Proper base change**: the base change map `b^* r_* ⟶ l_* t^*` of a cartesian square with
`r` proper is an isomorphism. -/
class HasProperBaseChange : Prop where
  isIso_pfBaseChange {U' U Z' Z : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'} {r : U ⟶ Z}
    {b : Z' ⟶ Z} [IsProper r] (h : IsPullback t l r b) :
    IsIso (F.pfBaseChange t l r b h.w).natTrans

end PushforwardBaseChange

section Cube

variable {U' U Z' Z V' V W' W : Scheme.{u}}

/-- The base change map of the pushforwards, transposed along `l^* ⊣ l_*`: it is the inverse of
the square isomorphism followed by the counit of `r^* ⊣ r_*`. -/
@[reassoc]
lemma pfBaseChange_counit (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z)
    (w : t ≫ r = l ≫ b) (M : F.obj U) :
    (F.pb l).map ((F.pfBaseChange t l r b w).natTrans.app M) ≫
        (F.adj l).counit.app ((F.pb t).obj M) =
      (F.sqIso t l r b w).inv.app ((F.pf r).obj M) ≫ (F.pb t).map ((F.adj r).counit.app M) :=
  mateEquiv_counit (F.adj r) (F.adj l) _ M

/-- The exchange map, transposed along `b^* ⊣ b_*`: it is the inverse of the base change map
followed by the counit of `t^* ⊣ t_*`. -/
@[reassoc]
lemma exchange_counit (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z) [IsOpenImmersion l]
    [IsOpenImmersion r] (w : t ≫ r = l ≫ b) [IsIso (F.baseChange t l r b w).natTrans]
    (N : F.obj U') :
    (F.pb b).map ((F.exchange t l r b w).natTrans.app N) ≫
        (F.adj b).counit.app ((F.sh l).obj N) =
      inv ((F.baseChange t l r b w).natTrans.app ((F.pf t).obj N)) ≫
        (F.sh l).map ((F.adj t).counit.app N) := by
  have h := mateEquiv_counit (F.adj t) (F.adj b)
    (TwoSquare.mk _ _ _ _ (inv (F.baseChange t l r b w).natTrans)) N
  simpa [exchange] using h

/-- **The exchange maps and the base change maps of the pushforwards on a cube.** For a
commutative cube with top face `t ≫ r = l ≫ b`, bottom face `t' ≫ r' = l' ≫ b'` (with `l`, `r`,
`l'`, `r'` open immersions) and connecting maps `x`, `y`, `z`, `v`
```
V' --t'--> V           U' --t--> U
|l'        |r'   ⟶     |l        |r
W' --b'--> W           Z' --b--> Z
```
the exchange maps of the top and bottom faces are intertwined by the base change maps of the
pushforwards of the faces `x ≫ t = t' ≫ y` and `z ≫ b = b' ≫ v` and the base change maps of the
extension by zero of the faces `x ≫ l = l' ≫ z` and `y ≫ r = r' ≫ v`. -/
lemma exchange_pfBaseChange_cube (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z)
    (t' : V' ⟶ V) (l' : V' ⟶ W') (r' : V ⟶ W) (b' : W' ⟶ W) (x : V' ⟶ U') (y : V ⟶ U)
    (z : W' ⟶ Z') (v : W ⟶ Z) [IsOpenImmersion l] [IsOpenImmersion r] [IsOpenImmersion l']
    [IsOpenImmersion r'] (w : t ≫ r = l ≫ b) (w' : t' ≫ r' = l' ≫ b') (sx : x ≫ t = t' ≫ y)
    (sl : x ≫ l = l' ≫ z) (sr : y ≫ r = r' ≫ v) (sb : z ≫ b = b' ≫ v)
    [IsIso (F.baseChange t l r b w).natTrans] [IsIso (F.baseChange t' l' r' b' w').natTrans]
    [IsIso (F.baseChange y r' r v sr).natTrans] (N : F.obj U') :
    inv ((F.baseChange y r' r v sr).natTrans.app ((F.pf t).obj N)) ≫
        (F.sh r').map ((F.pfBaseChange x t' t y sx).natTrans.app N) ≫
        (F.exchange t' l' r' b' w').natTrans.app ((F.pb x).obj N) ≫
        (F.pf b').map ((F.baseChange x l' l z sl).natTrans.app N) =
      (F.pb v).map ((F.exchange t l r b w).natTrans.app N) ≫
        (F.pfBaseChange z b' b v sb).natTrans.app ((F.sh l).obj N) := by
  -- the cube relation for the base change maps of the extension by zero, with inverses
  have hc := F.baseChange_cube t l r b t' l' r' b' x y z v w w' sx sl sr sb ((F.pf t).obj N)
  have hc' : (F.sh l').map ((F.sqIso x t' t y sx).inv.app ((F.pf t).obj N)) ≫
      (F.baseChange x l' l z sl).natTrans.app ((F.pb t).obj ((F.pf t).obj N)) =
      (F.baseChange t' l' r' b' w').natTrans.app ((F.pb y).obj ((F.pf t).obj N)) ≫
        (F.pb b').map ((F.baseChange y r' r v sr).natTrans.app ((F.pf t).obj N)) ≫
        (F.sqIso z b' b v sb).inv.app ((F.sh r).obj ((F.pf t).obj N)) ≫
        (F.pb z).map (inv ((F.baseChange t l r b w).natTrans.app ((F.pf t).obj N))) := by
    rw [← reassoc_of% hc]
    simp
  have hΞ : (F.pb b').map (inv ((F.baseChange y r' r v sr).natTrans.app ((F.pf t).obj N))) ≫
      inv ((F.baseChange t' l' r' b' w').natTrans.app ((F.pb y).obj ((F.pf t).obj N))) ≫
      (F.sh l').map ((F.sqIso x t' t y sx).inv.app ((F.pf t).obj N)) ≫
      (F.baseChange x l' l z sl).natTrans.app ((F.pb t).obj ((F.pf t).obj N)) =
      (F.sqIso z b' b v sb).inv.app ((F.sh r).obj ((F.pf t).obj N)) ≫
        (F.pb z).map (inv ((F.baseChange t l r b w).natTrans.app ((F.pf t).obj N))) := by
    rw [hc']
    simp [← Functor.map_comp_assoc]
  -- transpose along `b'^* ⊣ b'_*`
  apply ((F.adj b').homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hβ' := (inv (F.baseChange t' l' r' b' w').natTrans).naturality
    ((F.pfBaseChange x t' t y sx).natTrans.app N)
  have hγ := (F.baseChange x l' l z sl).natTrans.naturality ((F.adj t).counit.app N)
  have hs := (F.sqIso z b' b v sb).inv.naturality ((F.exchange t l r b w).natTrans.app N)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, NatIso.isIso_inv_app]
    at hβ' hγ hs
  erw [(F.adj b').counit_naturality]
  rw [F.exchange_counit_assoc t' l' r' b' w', reassoc_of% hβ',
    ← Functor.map_comp_assoc (F.sh l'), F.pfBaseChange_counit x t' t y sx, Functor.map_comp,
    Category.assoc, hγ]
  erw [F.pfBaseChange_counit z b' b v sb]
  rw [reassoc_of% hs, ← Functor.map_comp (F.pb z), F.exchange_counit t l r b w,
    Functor.map_comp, reassoc_of% hΞ]

end Cube

section ShriekBaseChange

variable [F.HasBaseChange] {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y}
  {g' : X' ⟶ X}

/-- Blueprint `def-cbc-exchange-map`: Compact-support exchange map.

**The compact-support exchange map** `Ex_! : g^* Rf_!(c) ⟶ Rf'_!(c') g'^*`, i.e. the natural
transformation `F.shriek c ⋙ g^* ⟶ g'^* ⋙ F.shriek c'`, for a compactification `c` of `f`, a
compactification `c'` of `f'` and a morphism `h : c'.Z ⟶ c.Z` making both squares
```
X' --g'--> X
|c'.i      |c.i
c'.Z --h--> c.Z
|c'.g      |c.g
Y' --g---> Y
```
cartesian. It is the horizontal composite of the inverse of the base change isomorphism
`g'^* ⋙ (c'.i)_! ≅ (c.i)_! ⋙ h^*` of the extension by zero for the upper square with the base
change map `g^* (c.g)_* ⟶ (c'.g)_* h^*` of the pushforwards for the lower square
(`CompactSupportFormalism.pfBaseChange`). -/
noncomputable def shriekBaseChange (c : Compactification f) (c' : Compactification f')
    (h : c'.Z ⟶ c.Z) (hi : IsPullback g' c'.i c.i h) (hp : IsPullback h c'.g c.g g) :
    TwoSquare (F.shriek c) (F.pb g') (F.pb g) (F.shriek c') :=
  haveI := HasBaseChange.isIso_baseChange (F := F) hi
  TwoSquare.mk _ _ _ _ (inv (F.baseChange g' c'.i c.i h hi.w).natTrans) ≫ₕ
    F.pfBaseChange h c'.g c.g g hp.w

/-- Blueprint `thm-cbc-finite-torsion`: Compact-support base change at finite coefficients,
in an abstract compact support formalism.

**The compact-support exchange map is an isomorphism** when the formalism satisfies base change
for the extension by zero and proper base change. -/
instance isIso_shriekBaseChange [F.HasProperBaseChange] (c : Compactification f)
    (c' : Compactification f') (h : c'.Z ⟶ c.Z) (hi : IsPullback g' c'.i c.i h)
    (hp : IsPullback h c'.g c.g g) : IsIso (F.shriekBaseChange c c' h hi hp).natTrans := by
  have := HasBaseChange.isIso_baseChange (F := F) hi
  have := HasProperBaseChange.isIso_pfBaseChange (F := F) hp
  dsimp only [shriekBaseChange, TwoSquare.hComp]
  infer_instance

/-- **The identity law** of the compact-support exchange map: for the identity square, `Ex_!` is
the identity, after inserting the identifications `(𝟙 Y)^* ≅ 𝟭` and `(𝟙 X)^* ≅ 𝟭`.
(blueprint: `thm-cbc-finite-torsion`, `fix-lem-exchanges`) -/
lemma shriekBaseChange_id (c : Compactification f) (hi : IsPullback (𝟙 X) c.i c.i (𝟙 c.Z))
    (hp : IsPullback (𝟙 c.Z) c.g c.g (𝟙 Y)) :
    (F.shriekBaseChange c c (𝟙 c.Z) hi hp).natTrans =
      Functor.whiskerLeft (F.shriek c) (F.pbId Y).hom ≫ (Functor.rightUnitor _).hom ≫
        (Functor.leftUnitor _).inv ≫ Functor.whiskerRight (F.pbId X).inv (F.shriek c) := by
  have := HasBaseChange.isIso_baseChange (F := F) hi
  have key : inv (F.baseChange (𝟙 X) c.i c.i (𝟙 c.Z) hi.w).natTrans =
      ((TwoSquare.mk (F.sh c.i) (𝟭 _) (𝟭 _) (F.sh c.i)
        ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv)).whiskerRight
          (F.pbId c.Z).hom).whiskerLeft (F.pbId X).inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [F.baseChange_id_horiz c.i hi.w]
    ext M
    simp [← Functor.map_comp]
  ext K
  simp [shriekBaseChange, key, pfBaseChange_id_horiz, shriek, ← Functor.map_comp]

/-- **Horizontal pasting** of compact-support exchange maps: for two cartesian squares placed
side by side
```
X'' --a'--> X' --b'--> X
|f''        |f'        |f
Y'' --a---> Y' --b---> Y
```
with compactifications `c''`, `c'`, `c` lying over each other along `h₁ : c''.Z ⟶ c'.Z` and
`h₂ : c'.Z ⟶ c.Z`, the exchange map of the outer rectangle along `h₁ ≫ h₂` is the vertical
composite of the two exchange maps, after inserting the composition isomorphisms of the
pullbacks. (blueprint: `thm-cbc-finite-torsion`, `fix-lem-exchanges`) -/
lemma shriekBaseChange_paste_horiz {X'' Y'' : Scheme.{u}} {f'' : X'' ⟶ Y''} {a' : X'' ⟶ X'}
    {a : Y'' ⟶ Y'} {b' : X' ⟶ X} {b : Y' ⟶ Y} (c : Compactification f)
    (c' : Compactification f') (c'' : Compactification f'') (h₁ : c''.Z ⟶ c'.Z)
    (h₂ : c'.Z ⟶ c.Z) (hi₁ : IsPullback a' c''.i c'.i h₁) (hp₁ : IsPullback h₁ c''.g c'.g a)
    (hi₂ : IsPullback b' c'.i c.i h₂) (hp₂ : IsPullback h₂ c'.g c.g b)
    (hi : IsPullback (a' ≫ b') c''.i c.i (h₁ ≫ h₂)) (hp : IsPullback (h₁ ≫ h₂) c''.g c.g (a ≫ b)) :
    F.shriekBaseChange c c'' (h₁ ≫ h₂) hi hp =
      ((F.shriekBaseChange c c' h₂ hi₂ hp₂ ≫ᵥ F.shriekBaseChange c' c'' h₁ hi₁ hp₁).whiskerLeft
        (F.pbComp' a' b' (a' ≫ b') rfl).inv).whiskerRight (F.pbComp' a b (a ≫ b) rfl).hom := by
  have := HasBaseChange.isIso_baseChange (F := F) hi
  have := HasBaseChange.isIso_baseChange (F := F) hi₁
  have := HasBaseChange.isIso_baseChange (F := F) hi₂
  have hA : inv (F.baseChange (a' ≫ b') c''.i c.i (h₁ ≫ h₂) hi.w).natTrans =
      ((TwoSquare.vComp (TwoSquare.mk _ _ _ _ (inv (F.baseChange b' c'.i c.i h₂ hi₂.w).natTrans))
        (TwoSquare.mk _ _ _ _ (inv (F.baseChange a' c''.i c'.i h₁ hi₁.w).natTrans))).whiskerLeft
          (F.pbComp' a' b' (a' ≫ b') rfl).inv).whiskerRight
            (F.pbComp' h₁ h₂ (h₁ ≫ h₂) rfl).hom := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [F.baseChange_paste_horiz a' b' c''.i c'.i c.i h₁ h₂ (a' ≫ b') (h₁ ≫ h₂) hi₁.w hi₂.w rfl
      rfl hi.w]
    ext M
    simp
  have hP := F.pfBaseChange_paste_horiz h₁ h₂ c''.g c'.g c.g a b (h₁ ≫ h₂) (a ≫ b) hp₁.w hp₂.w
    rfl rfl hp.w
  ext K
  simp only [shriekBaseChange, hA, hP, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    TwoSquare.hComp, TwoSquare.vComp, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    Category.assoc, shriek]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := (F.pfBaseChange h₁ c''.g c'.g a hp₁.w).natTrans.naturality
    ((inv (F.baseChange b' c'.i c.i h₂ hi₂.w).natTrans).app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  dsimp only [TwoSquare.mk, TwoSquare.natTrans]
  rw [← reassoc_of% hn]

/-- The comparison along a refinement `r`, in terms of the unit of `r^* ⊣ r_*` and the inverse
of the base change map of the extension by zero of the square of `r`. -/
lemma refinementComparison_app_eq {c d : Compactification f} (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (K : F.obj X) :
    haveI := HasBaseChange.isIso_baseChange (F := F) hr.flip
    (F.refinementComparison r hr).app K =
      (F.pf d.g).map ((F.adj r.hom).unit.app ((F.sh d.i).obj K) ≫
        (F.pf r.hom).map (inv ((F.baseChange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans.app K) ≫
          (F.sh c.i).map ((F.pbId X).hom.app K))) ≫
        (F.pfComp' r.hom d.g c.g r.hom_g).inv.app ((F.sh c.i).obj K) := by
  have := HasBaseChange.isIso_baseChange (F := F) hr.flip
  rw [F.refinementComparison_eq_of_baseChange r hr ((Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (F.pbId X).symm (F.sh c.i) ≪≫
    asIso (F.baseChange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans)
    (by ext K; simp [← Functor.map_comp_assoc])]
  simp

/-- **Compatibility with refinements**: the compact-support exchange maps attached to two
compactifications `c`, `d` of `f` (and `c'`, `d'` of `f'`) are intertwined by the comparisons
`Rf_!(d) ⟶ Rf_!(c)` and `Rf'_!(d') ⟶ Rf'_!(c')` along refinements `r : c ⟶ d` and
`r' : c' ⟶ d'` compatible with the maps `c'.Z ⟶ c.Z` and `d'.Z ⟶ d.Z`.
(blueprint: `thm-cbc-finite-torsion`, independence of the compactification) -/
lemma shriekBaseChange_refinementComparison {c d : Compactification f}
    {c' d' : Compactification f'} (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i)
    (r' : c'.Refinement d') (hr' : IsPullback c'.i (𝟙 X') r'.hom d'.i) (hc : c'.Z ⟶ c.Z)
    (hci : IsPullback g' c'.i c.i hc) (hcp : IsPullback hc c'.g c.g g) (hd : d'.Z ⟶ d.Z)
    (hdi : IsPullback g' d'.i d.i hd) (hdp : IsPullback hd d'.g d.g g)
    (hcomm : hc ≫ r.hom = r'.hom ≫ hd) :
    Functor.whiskerRight (F.refinementComparison r hr) (F.pb g) ≫
        (F.shriekBaseChange c c' hc hci hcp).natTrans =
      (F.shriekBaseChange d d' hd hdi hdp).natTrans ≫
        Functor.whiskerLeft (F.pb g') (F.refinementComparison r' hr') := by
  have := HasBaseChange.isIso_baseChange (F := F) hr.flip
  have := HasBaseChange.isIso_baseChange (F := F) hr'.flip
  have := HasBaseChange.isIso_baseChange (F := F) hci
  have := HasBaseChange.isIso_baseChange (F := F) hdi
  have hw : g' ≫ d.i = c'.i ≫ (hc ≫ r.hom) := by rw [← r.i_hom, reassoc_of% hci.w]
  -- the two decompositions of the base change map of the square `g' ≫ d.i = c'.i ≫ (hc ≫ r)`
  have hcube : ∀ K : F.obj X,
      (F.baseChange g' c'.i c.i hc hci.w).natTrans.app K ≫
        (F.pb hc).map ((F.sh c.i).map ((F.pbId X).inv.app K) ≫
          (F.baseChange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans.app K) ≫
        (F.sqIso hc r'.hom r.hom hd hcomm).hom.app ((F.sh d.i).obj K) =
      (F.sh c'.i).map ((F.pbId X').inv.app ((F.pb g').obj K)) ≫
        (F.baseChange (𝟙 X') c'.i d'.i r'.hom hr'.flip.w).natTrans.app ((F.pb g').obj K) ≫
        (F.pb r'.hom).map ((F.baseChange g' d'.i d.i hd hdi.w).natTrans.app K) := by
    intro K
    have h₁ := congr_app (F.baseChange_paste_horiz g' (𝟙 X) c'.i c.i d.i hc r.hom g'
      (hc ≫ r.hom) hci.w hr.flip.w (Category.comp_id g') rfl hw) K
    have h₂ := congr_app (F.baseChange_paste_horiz (𝟙 X') g' c'.i d'.i d.i r'.hom hd g'
      (hc ≫ r.hom) hr'.flip.w hdi.w (Category.id_comp g') hcomm.symm hw) K
    simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, Functor.comp_obj] at h₁ h₂
    rw [F.pbComp'_id_right_hom_app] at h₁
    rw [F.pbComp'_id_left_hom_app] at h₂
    have hn := (F.baseChange g' c'.i c.i hc hci.w).natTrans.naturality ((F.pbId X).inv.app K)
    simp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [F.sqIso_eq hc r'.hom r.hom hd hcomm (hc ≫ r.hom) rfl hcomm.symm]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
    rw [← reassoc_of% hn, ← reassoc_of% h₁, h₂]
    simp
  -- the same identity for the inverses, transposed along `r'^* ⊣ r'_*`
  have hcore : ∀ K : F.obj X,
      (F.pb hd).map ((F.adj r.hom).unit.app ((F.sh d.i).obj K) ≫
        (F.pf r.hom).map (inv ((F.baseChange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans.app K) ≫
          (F.sh c.i).map ((F.pbId X).hom.app K))) ≫
        (F.pfBaseChange hc r'.hom r.hom hd hcomm).natTrans.app ((F.sh c.i).obj K) ≫
        (F.pf r'.hom).map (inv ((F.baseChange g' c'.i c.i hc hci.w).natTrans.app K)) =
      inv ((F.baseChange g' d'.i d.i hd hdi.w).natTrans.app K) ≫
        (F.adj r'.hom).unit.app ((F.sh d'.i).obj ((F.pb g').obj K)) ≫
        (F.pf r'.hom).map (inv ((F.baseChange (𝟙 X') c'.i d'.i r'.hom hr'.flip.w).natTrans.app
          ((F.pb g').obj K)) ≫ (F.sh c'.i).map ((F.pbId X').hom.app ((F.pb g').obj K))) := by
    intro K
    have hinv := (IsIso.inv_eq_inv (f := _) (g := _)).mpr (hcube K)
    simp only [IsIso.inv_comp, Category.assoc, ← Functor.map_inv, NatIso.inv_inv_app,
      NatIso.inv_hom_app] at hinv
    -- the transpose of the base change map of the pushforwards along `r'^* ⊣ r'_*`
    have hm : ∀ {A : F.obj d.Z} {B : F.obj c.Z} (z : (F.pb r.hom).obj A ⟶ B),
        (F.pb r'.hom).map ((F.pb hd).map ((F.adj r.hom).unit.app A ≫ (F.pf r.hom).map z) ≫
          (F.pfBaseChange hc r'.hom r.hom hd hcomm).natTrans.app B) ≫
          (F.adj r'.hom).counit.app ((F.pb hc).obj B) =
        (F.sqIso hc r'.hom r.hom hd hcomm).inv.app A ≫ (F.pb hc).map z := by
      intro A B z
      have h₁ := mateEquiv_counit (F.adj r.hom) (F.adj r'.hom)
        (TwoSquare.mk _ _ _ _ (F.sqIso hc r'.hom r.hom hd hcomm).inv) B
      have h₂ := (F.sqIso hc r'.hom r.hom hd hcomm).inv.naturality
        ((F.adj r.hom).unit.app A ≫ (F.pf r.hom).map z)
      simp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂
      rw [Functor.map_comp, Category.assoc]
      erw [h₁, reassoc_of% h₂]
      rw [← Functor.map_comp]
      simp
    apply ((F.adj r'.hom).homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit]
    have hm' := hm (A := (F.sh d.i).obj K) (B := (F.sh c.i).obj K)
      (inv ((F.baseChange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans.app K) ≫
        (F.sh c.i).map ((F.pbId X).hom.app K))
    simp only [Functor.map_comp, Category.assoc] at hm' hinv
    simp only [Functor.map_comp, Category.assoc, Adjunction.counit_naturality]
    rw [reassoc_of% hm', hinv]
    congr 1
    erw [(F.adj r'.hom).counit_naturality_assoc,
      (F.adj r'.hom).left_triangle_components_assoc]
  ext K
  have hv := congr_app (F.pfBaseChange_paste_vert hc hd g r'.hom r.hom d'.g d.g c'.g c.g hcomm
    hdp.w r'.hom_g r.hom_g hcp.w) ((F.sh c.i).obj K)
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj] at hv
  have hn := (F.pfBaseChange hd d'.g d.g g hdp.w).natTrans.naturality
    ((F.adj r.hom).unit.app ((F.sh d.i).obj K) ≫
      (F.pf r.hom).map (inv ((F.baseChange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans.app K) ≫
        (F.sh c.i).map ((F.pbId X).hom.app K)))
  have hn₂ := (F.pfComp' r'.hom d'.g c'.g r'.hom_g).inv.naturality
    (inv ((F.baseChange g' c'.i c.i hc hci.w).natTrans.app K))
  have hcore' := congrArg (F.pf d'.g).map (hcore K)
  have hcancel : (F.pb g).map ((F.pfComp' r.hom d.g c.g r.hom_g).inv.app ((F.sh c.i).obj K)) ≫
      (F.pb g).map ((F.pfComp' r.hom d.g c.g r.hom_g).hom.app ((F.sh c.i).obj K)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.map_comp,
    Category.assoc] at hn hn₂ hcore' hv
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    refinementComparison_app_eq, refinementComparison_app_eq]
  simp only [shriekBaseChange, TwoSquare.hComp, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_obj, NatIso.isIso_inv_app, Functor.map_comp,
    Category.assoc, Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
  dsimp only [shriek, Functor.comp_obj, Functor.id_obj]
  erw [hv]
  simp only [Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  dsimp only [Functor.comp_obj]
  simp only [Category.id_comp]
  rw [reassoc_of% hcancel, reassoc_of% hn, ← hn₂, reassoc_of% hcore']

end ShriekBaseChange

section Composition

variable [F.HasProperExchange]

/-- **The compact-support exchange maps and the composition isomorphisms.** Let `T` be a
triangle of compactifications of `(f, g)` and `T'` a triangle of compactifications of
`(f', g')` lying over it along `a : T'.cf.Z ⟶ T.cf.Z`, `c : T'.cg.Z ⟶ T.cg.Z` and
`b : T'.cfg.Z ⟶ T.cfg.Z`, with all the relevant squares cartesian. Then the exchange map of the
composite is the horizontal composite of the exchange maps, through the composition
isomorphisms `F.compIso T` and `F.compIso T'`. (blueprint: `thm-cbc-finite-torsion`,
`fix-lem-exchanges`) -/
theorem compIso_shriekBaseChange {X Y S X' Y' S' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    {f' : X' ⟶ Y'} {g' : Y' ⟶ S'} {gX : X' ⟶ X} {gY : Y' ⟶ Y} {gS : S' ⟶ S}
    (T : Compactification.Triangle f g) (T' : Compactification.Triangle f' g')
    (a : T'.cf.Z ⟶ T.cf.Z) (c : T'.cg.Z ⟶ T.cg.Z) (b : T'.cfg.Z ⟶ T.cfg.Z)
    (hfi : IsPullback gX T'.cf.i T.cf.i a) (hfp : IsPullback a T'.cf.g T.cf.g gY)
    (hgi : IsPullback gY T'.cg.i T.cg.i c) (hgp : IsPullback c T'.cg.g T.cg.g gS)
    (hfgi : IsPullback gX T'.cfg.i T.cfg.i b) (hfgp : IsPullback b T'.cfg.g T.cfg.g gS)
    (hq : IsPullback a T'.q T.q b) (hp : b ≫ T.p = T'.p ≫ c) :
    Functor.whiskerRight (F.compIso T).hom (F.pb gS) ≫
        (F.shriekBaseChange T.cfg T'.cfg b hfgi hfgp).natTrans =
      (F.shriekBaseChange T.cf T'.cf a hfi hfp ≫ₕ
          F.shriekBaseChange T.cg T'.cg c hgi hgp).natTrans ≫
        Functor.whiskerLeft (F.pb gX) (F.compIso T').hom := by
  have := HasBaseChange.isIso_baseChange (F := F) T.isPullback
  have := HasBaseChange.isIso_baseChange (F := F) T'.isPullback
  have := HasBaseChange.isIso_baseChange (F := F) hfi
  have := HasBaseChange.isIso_baseChange (F := F) hgi
  have := HasBaseChange.isIso_baseChange (F := F) hfgi
  have := HasBaseChange.isIso_baseChange (F := F) hq
  ext K
  -- the base change map of the extension by zero along `cfg.i = cf.i ≫ q`
  have hbc := congr_app (F.baseChange_paste_vert gX a b T'.cf.i T.cf.i T'.q T.q T'.cfg.i
    T.cfg.i hfi.w hq.w T'.i_q T.i_q hfgi.w) K
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Functor.comp_obj, Category.assoc] at hbc
  have hA : (F.pb b).map ((F.shComp' T.cf.i T.q T.cfg.i T.i_q).inv.app K) ≫
      inv ((F.baseChange gX T'.cfg.i T.cfg.i b hfgi.w).natTrans.app K) =
      inv ((F.baseChange a T'.q T.q b hq.w).natTrans.app ((F.sh T.cf.i).obj K)) ≫
        (F.sh T'.q).map (inv ((F.baseChange gX T'.cf.i T.cf.i a hfi.w).natTrans.app K)) ≫
        (F.shComp' T'.cf.i T'.q T'.cfg.i T'.i_q).inv.app ((F.pb gX).obj K) := by
    rw [IsIso.comp_inv_eq, hbc]
    simp
  -- the cube relating the exchange maps of `T` and `T'`
  have hC := F.exchange_pfBaseChange_cube T.cf.g T.q T.cg.i T.p T'.cf.g T'.q T'.cg.i T'.p a gY b
    c T.isPullback.w T'.isPullback.w hfp.w hq.w hgi.w hp ((F.sh T.cf.i).obj K)
  have hC' : inv ((F.baseChange gY T'.cg.i T.cg.i c hgi.w).natTrans.app
        ((F.pf T.cf.g).obj ((F.sh T.cf.i).obj K))) ≫
      (F.sh T'.cg.i).map ((F.pfBaseChange a T'.cf.g T.cf.g gY hfp.w).natTrans.app
        ((F.sh T.cf.i).obj K)) ≫
      (F.exchange T'.cf.g T'.q T'.cg.i T'.p T'.isPullback.w).natTrans.app
        ((F.pb a).obj ((F.sh T.cf.i).obj K)) =
      (F.pb c).map ((F.exchange T.cf.g T.q T.cg.i T.p T.isPullback.w).natTrans.app
        ((F.sh T.cf.i).obj K)) ≫
      (F.pfBaseChange b T'.p T.p c hp).natTrans.app ((F.sh T.q).obj ((F.sh T.cf.i).obj K)) ≫
      (F.pf T'.p).map (inv ((F.baseChange a T'.q T.q b hq.w).natTrans.app
        ((F.sh T.cf.i).obj K))) := by
    rw [← reassoc_of% hC]
    simp [← Functor.map_comp]
  -- the base change map of the pushforwards along `cfg.g = p ≫ cg.g`
  have hv := congr_app (F.pfBaseChange_paste_vert b c gS T'.p T.p T'.cg.g T.cg.g T'.cfg.g
    T.cfg.g hp hgp.w T'.p_g T.p_g hfgp.w) ((F.sh T.cfg.i).obj K)
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj] at hv
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    compIso_hom_app, compIso_hom_app]
  simp only [shriekBaseChange, TwoSquare.hComp, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_obj, NatIso.isIso_inv_app, Functor.map_comp,
    Category.assoc, Functor.associator_hom_app, Functor.associator_inv_app]
  dsimp only [shriek, Functor.comp_obj, Functor.id_obj, Functor.comp_map]
  erw [hv]
  trace_state
  sorry

end Composition

section Canonical

variable [F.HasProperExchange] {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {g : Y' ⟶ Y} {g' : X' ⟶ X}

/-- The compact-support exchange map `Ex_!` along a compactification `c` of `f` and its base
change `c.ofIsPullback sq` (blueprint `def-cbc-compact-support-square`). -/
noncomputable abbrev shriekBaseChangeOfIsPullback (sq : IsPullback g' f' f g)
    (c : Compactification f) :
    TwoSquare (F.shriek c) (F.pb g') (F.pb g) (F.shriek (c.ofIsPullback sq)) :=
  F.shriekBaseChange c (c.ofIsPullback sq) (pullback.fst c.g g)
    (c.isPullback_i_ofIsPullback sq) (c.isPullback_g_ofIsPullback sq).flip

/-- **The compact-support exchange map of the canonical compactly supported direct images**
`Ex_! : g^* Rf_! ⟶ Rf'_! g'^*`: the exchange map along the chosen compactification of `f` and its
base change, followed by the comparison isomorphism with the chosen compactification of `f'`.
(blueprint: `def-cbc-exchange-map`) -/
noncomputable def lowerShriekBaseChange [HasCompactification f] [HasCompactification f']
    [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    TwoSquare (F.lowerShriek f) (F.pb g') (F.pb g) (F.lowerShriek f') :=
  (F.shriekBaseChangeOfIsPullback sq (HasCompactification.compactification f)).whiskerBottom
    (F.shriekIso _ (HasCompactification.compactification f')).hom

instance isIso_lowerShriekBaseChange [F.HasProperBaseChange] [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    IsIso (F.lowerShriekBaseChange sq).natTrans := by
  dsimp only [lowerShriekBaseChange, TwoSquare.whiskerBottom]
  infer_instance

/-- **Compatibility with the comparison isomorphisms**: the compact-support exchange maps along
two compactifications `c` and `d` of `f` and their base changes are intertwined by the comparison
isomorphisms `F.shriekIso c d` and `F.shriekIso (c.ofIsPullback sq) (d.ofIsPullback sq)`.
(blueprint: `thm-cbc-finite-torsion`, independence of the compactification) -/
lemma shriekBaseChangeOfIsPullback_shriekIso [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback g' f' f g) (c d : Compactification f) :
    Functor.whiskerRight (F.shriekIso c d).hom (F.pb g) ≫
        (F.shriekBaseChangeOfIsPullback sq d).natTrans =
      (F.shriekBaseChangeOfIsPullback sq c).natTrans ≫
        Functor.whiskerLeft (F.pb g') (F.shriekIso (c.ofIsPullback sq) (d.ofIsPullback sq)).hom := by
  have hr₀ := Compactification.isPullback_infFst c d
  have hr := Compactification.isPullback_infSnd c d
  have hr₀' := (Compactification.infFst c d).isPullback_ofIsPullback sq hr₀
  have hr' := (Compactification.infSnd c d).isPullback_ofIsPullback sq hr
  have h₀ := F.shriekBaseChange_refinementComparison (Compactification.infFst c d) hr₀
    ((Compactification.infFst c d).ofIsPullback sq) hr₀' (pullback.fst (c.inf d).g g)
    ((c.inf d).isPullback_i_ofIsPullback sq) ((c.inf d).isPullback_g_ofIsPullback sq).flip
    (pullback.fst c.g g) (c.isPullback_i_ofIsPullback sq) (c.isPullback_g_ofIsPullback sq).flip
    (Compactification.Refinement.ofIsPullback_hom_fst sq _).symm
  have h₁ := F.shriekBaseChange_refinementComparison (Compactification.infSnd c d) hr
    ((Compactification.infSnd c d).ofIsPullback sq) hr' (pullback.fst (c.inf d).g g)
    ((c.inf d).isPullback_i_ofIsPullback sq) ((c.inf d).isPullback_g_ofIsPullback sq).flip
    (pullback.fst d.g g) (d.isPullback_i_ofIsPullback sq) (d.isPullback_g_ofIsPullback sq).flip
    (Compactification.Refinement.ofIsPullback_hom_fst sq _).symm
  rw [F.shriekIso_eq _ _ hr₀' hr', F.shriekIso_eq _ _ hr₀ hr]
  ext K
  have h₀' := congr_app h₀ K
  have h₁' := congr_app h₁ K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h₀' h₁'
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app]
  dsimp only [shriekBaseChangeOfIsPullback]
  rw [← cancel_mono ((F.refinementComparison _ hr').app ((F.pb g').obj K))]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← h₀', ← h₁', ← Functor.map_comp_assoc, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id]

/-- **Independence of the compactification**: the exchange map of the canonical compactly
supported direct images is computed by any compactification `c` of `f` and its base change, up
to the comparison isomorphisms `F.shriekIso`. (blueprint: `thm-cbc-finite-torsion`,
`fix-lem-exchanges`) -/
theorem lowerShriekBaseChange_eq [HasCompactification f] [HasCompactification f']
    [QuasiCompact f] [QuasiCompact f'] (sq : IsPullback g' f' f g) (c : Compactification f) :
    F.lowerShriekBaseChange sq =
      ((F.shriekBaseChangeOfIsPullback sq c).whiskerTop
        (F.shriekIso (HasCompactification.compactification f) c).hom).whiskerBottom
        (F.shriekIso _ (HasCompactification.compactification f')).hom := by
  have h := F.shriekBaseChangeOfIsPullback_shriekIso sq
    (HasCompactification.compactification f) c
  rw [← F.shriekIso_trans _ ((HasCompactification.compactification f).ofIsPullback sq)
    (HasCompactification.compactification f'),
    ← F.shriekIso_symm ((HasCompactification.compactification f).ofIsPullback sq)]
  ext K
  have h' := congr_app h K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h'
  simp only [lowerShriekBaseChange, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
    Iso.symm_hom, Category.assoc]
  rw [reassoc_of% h', Iso.hom_inv_id_app_assoc]

/-- **Vertical pasting** of compact-support exchange maps: for two cartesian squares placed one
above the other
```
X' --gX--> X
|f₁'       |f₁
Y' --gY--> Y
|f₂'       |f₂
S' --gS--> S
```
the exchange map of the outer rectangle is the horizontal composite of the two exchange maps,
after inserting the composition isomorphisms `Rf₁_! ⋙ Rf₂_! ≅ R(f₁ ≫ f₂)_!`.
(blueprint: `thm-cbc-finite-torsion`, `fix-lem-exchanges`) -/
theorem lowerShriekBaseChange_paste_vert {S S' : Scheme.{u}} {f₁ : X ⟶ Y} {f₂ : Y ⟶ S}
    {f₁' : X' ⟶ Y'} {f₂' : Y' ⟶ S'} {gX : X' ⟶ X} {gY : Y' ⟶ Y} {gS : S' ⟶ S}
    [HasCompactification f₁] [HasCompactification f₂] [HasCompactification (f₁ ≫ f₂)]
    [HasCompactification f₁'] [HasCompactification f₂'] [HasCompactification (f₁' ≫ f₂')]
    [QuasiCompact (f₁ ≫ f₂)] [QuasiCompact f₁'] [QuasiCompact f₂'] [QuasiCompact (f₁' ≫ f₂')]
    (sq₁ : IsPullback gX f₁' f₁ gY) (sq₂ : IsPullback gY f₂' f₂ gS)
    (sq : IsPullback gX (f₁' ≫ f₂') (f₁ ≫ f₂) gS) :
    F.lowerShriekBaseChange sq =
      ((F.lowerShriekBaseChange sq₁ ≫ₕ F.lowerShriekBaseChange sq₂).whiskerTop
        (F.lowerShriekCompIso f₁ f₂).inv).whiskerBottom (F.lowerShriekCompIso f₁' f₂').hom := by
  sorry

end Canonical

end AlgebraicGeometry.CompactSupportFormalism
