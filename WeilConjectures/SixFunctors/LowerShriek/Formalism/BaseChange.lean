/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Canonical
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Identity
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Pasting

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
  simp [← Functor.map_comp]

/-- The base change map of the pushforwards of the square `𝟙 ≫ j = j ≫ 𝟙` is the identity, up
to `(𝟙)^* ≅ 𝟭`. -/
lemma pfBaseChange_id_horiz {X Y : Scheme.{u}} (j : X ⟶ Y) (w : 𝟙 X ≫ j = j ≫ 𝟙 Y) :
    F.pfBaseChange (𝟙 X) j j (𝟙 Y) w =
      ((TwoSquare.mk (F.pf j) (𝟭 _) (𝟭 _) (F.pf j)
        ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv)).whiskerRight
          (F.pbId Y).hom).whiskerLeft (F.pbId X).inv := by
  rw [pfBaseChange, sqIso_id_horiz_inv, mateEquiv_whiskerTop_whiskerBottom, mateEquiv_unitors]

/-- **Proper base change**: the base change map `b^* r_* ⟶ l_* t^*` of a cartesian square with
`r` proper is an isomorphism. -/
class HasProperBaseChange : Prop where
  isIso_pfBaseChange {U' U Z' Z : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'} {r : U ⟶ Z}
    {b : Z' ⟶ Z} [IsProper r] (h : IsPullback t l r b) :
    IsIso (F.pfBaseChange t l r b h.w).natTrans

end PushforwardBaseChange

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
  haveI := HasBaseChange.isIso_baseChange (F := F) hi
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
  sorry

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
  sorry

end ShriekBaseChange

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
  sorry

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
