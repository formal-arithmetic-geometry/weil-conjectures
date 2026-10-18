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
  have hpaste := F.pfBaseChange_paste_vert hc hd g r'.hom r.hom d'.g d.g c'.g c.g
    hcomm hdp.w r'.hom_g r.hom_g hcp.w
  ext K
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, F.refinementComparison_app_eq r hr K,
    F.refinementComparison_app_eq r' hr' ((F.pb g').obj K)]
  simp only [shriekBaseChange, hpaste, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj, Functor.map_comp, Category.assoc, NatIso.isIso_inv_app]
  have hcancel :
      (F.pb g).map ((F.pfComp' r.hom d.g c.g r.hom_g).inv.app ((F.sh c.i).obj K)) ≫
        (F.pb g).map ((F.pfComp' r.hom d.g c.g r.hom_g).hom.app ((F.sh c.i).obj K)) =
        𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app]
    exact (F.pb g).map_id _
  erw [Category.id_comp, Category.id_comp, reassoc_of% hcancel]
  have hn := (F.pfComp' r'.hom d'.g c'.g r'.hom_g).inv.naturality
    (inv ((F.baseChange g' c'.i c.i hc hci.w).natTrans.app K))
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  erw [← hn]
  have hz := (F.pfBaseChange hd d'.g d.g g hdp.w).natTrans.naturality
    ((F.adj r.hom).unit.app ((F.sh d.i).obj K) ≫
      (F.pf r.hom).map (inv ((F.baseChange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans.app K) ≫
        (F.sh c.i).map ((F.pbId X).hom.app K)))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.map_comp] at hz
  erw [reassoc_of% hz]
  have hh := congrArg (F.pf d'.g).map (hcore K)
  simp only [Functor.map_comp, Category.assoc] at hh
  erw [reassoc_of% hh]


end ShriekBaseChange

section BaseChangeCube

variable {A B C D A' B' C' D' : Scheme.{u}}
variable (r : A ⟶ B) (k : A ⟶ C) (i : B ⟶ D) (p : C ⟶ D)
  (r' : A' ⟶ B') (k' : A' ⟶ C') (i' : B' ⟶ D') (p' : C' ⟶ D')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C) (d : D' ⟶ D)
  [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion k'] [IsOpenImmersion i']
  (Q : IsPullback r k i p) (Q' : IsPullback r' k' i' p')
  (K : IsPullback a k' k c) (I : IsPullback b i' i d)
  (wr : a ≫ r = r' ≫ b) (wp : c ≫ p = p' ≫ d)

-- Compare the two horizontal decompositions of the same open-immersion cube.
private lemma baseChange_cube_hom_app (N : F.obj B) :
    (F.sh k').map ((F.sqIso a r' r b wr).hom.app N) ≫
      (F.baseChange r' k' i' p' Q'.w).natTrans.app ((F.pb b).obj N) ≫
      (F.pb p').map ((F.baseChange b i' i d I.w).natTrans.app N) ≫
      (F.sqIso c p' p d wp).inv.app ((F.sh i).obj N) =
    (F.baseChange a k' k c K.w).natTrans.app ((F.pb r).obj N) ≫
      (F.pb c).map ((F.baseChange r k i p Q.w).natTrans.app N) := by
  have w : (a ≫ r) ≫ i = k' ≫ (c ≫ p) := by
    rw [Category.assoc, Q.w, ← Category.assoc, K.w, Category.assoc]
  have h₁ := congr_app (F.baseChange_paste_horiz a r k' k i c p (a ≫ r) (c ≫ p)
    K.w Q.w rfl rfl w) N
  have h₂ := congr_app (F.baseChange_paste_horiz r' b k' i' i p' d (a ≫ r) (c ≫ p)
    Q'.w I.w wr.symm wp.symm w) N
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Functor.comp_obj] at h₁ h₂
  rw [F.sqIso_eq a r' r b wr (a ≫ r) rfl wr.symm,
    F.sqIso_eq c p' p d wp (c ≫ p) rfl wp.symm]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% h₂, h₁]
  simp [← Functor.map_comp_assoc]

-- Transpose the inverse cube equation along the two pushforward adjunctions.
set_option maxRecDepth 4000 in
private lemma exchange_cube_app [F.HasBaseChange] (M : F.obj A) :
    haveI := HasBaseChange.isIso_baseChange (F := F) Q
    haveI := HasBaseChange.isIso_baseChange (F := F) Q'
    haveI := HasBaseChange.isIso_baseChange (F := F) K
    haveI := HasBaseChange.isIso_baseChange (F := F) I
    (F.pb d).map ((F.exchange r k i p Q.w).natTrans.app M) ≫
      (F.pfBaseChange c p' p d wp).natTrans.app ((F.sh k).obj M) ≫
      (F.pf p').map (inv ((F.baseChange a k' k c K.w).natTrans.app M)) =
    inv ((F.baseChange b i' i d I.w).natTrans.app ((F.pf r).obj M)) ≫
      (F.sh i').map ((F.pfBaseChange a r' r b wr).natTrans.app M) ≫
      (F.exchange r' k' i' p' Q'.w).natTrans.app ((F.pb a).obj M) := by
  have := HasBaseChange.isIso_baseChange (F := F) Q
  have := HasBaseChange.isIso_baseChange (F := F) Q'
  have := HasBaseChange.isIso_baseChange (F := F) K
  have := HasBaseChange.isIso_baseChange (F := F) I
  have hcore (N : F.obj B) :
      (F.sqIso c p' p d wp).inv.app ((F.sh i).obj N) ≫
        (F.pb c).map (inv ((F.baseChange r k i p Q.w).natTrans.app N)) ≫
        inv ((F.baseChange a k' k c K.w).natTrans.app ((F.pb r).obj N)) =
      (F.pb p').map (inv ((F.baseChange b i' i d I.w).natTrans.app N)) ≫
        inv ((F.baseChange r' k' i' p' Q'.w).natTrans.app ((F.pb b).obj N)) ≫
        (F.sh k').map ((F.sqIso a r' r b wr).inv.app N) := by
    have hinv := (IsIso.inv_eq_inv (f := _) (g := _)).mpr
      (baseChange_cube_hom_app F r k i p r' k' i' p' a b c d Q Q' K I wr wp N)
    simp only [IsIso.inv_comp, Category.assoc, ← Functor.map_inv,
      NatIso.inv_inv_app, NatIso.inv_hom_app] at hinv
    rw [← hinv]
    simp
  have hp := mateEquiv_counit (F.adj p) (F.adj p')
    (TwoSquare.mk _ _ _ _ (F.sqIso c p' p d wp).inv) ((F.sh k).obj M)
  have hQ := mateEquiv_counit (F.adj r) (F.adj p)
    (TwoSquare.mk _ _ _ _ (inv (F.baseChange r k i p Q.w).natTrans)) M
  have hQ' := mateEquiv_counit (F.adj r') (F.adj p')
    (TwoSquare.mk _ _ _ _ (inv (F.baseChange r' k' i' p' Q'.w).natTrans))
    ((F.pb a).obj M)
  have hr := mateEquiv_counit (F.adj r) (F.adj r')
    (TwoSquare.mk _ _ _ _ (F.sqIso a r' r b wr).inv) M
  simp only [Functor.comp_obj, NatIso.isIso_inv_app] at hp hQ hQ' hr
  apply ((F.adj p').homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  erw [(F.adj p').counit_naturality, reassoc_of% hp]
  have hn := (F.sqIso c p' p d wp).inv.naturality
    ((F.exchange r k i p Q.w).natTrans.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  erw [reassoc_of% hn]
  rw [← Functor.map_comp_assoc]
  erw [hQ]
  rw [Functor.map_comp, Category.assoc]
  have hnK := (inv (F.baseChange a k' k c K.w).natTrans).naturality
    ((F.adj r).counit.app M)
  simp only [Functor.comp_map, Functor.comp_obj, NatIso.isIso_inv_app] at hnK
  erw [hnK]
  erw [hQ']
  have hnQ' := (inv (F.baseChange r' k' i' p' Q'.w).natTrans).naturality
    ((F.pfBaseChange a r' r b wr).natTrans.app M)
  simp only [Functor.comp_map, Functor.comp_obj, NatIso.isIso_inv_app] at hnQ'
  erw [reassoc_of% hnQ']
  rw [← Functor.map_comp]
  erw [hr]
  simp only [Functor.map_comp]
  erw [reassoc_of% hcore]

end BaseChangeCube

section TriangleBaseChange
variable {X Y X' Y' S S' : Scheme.{u}} {f₁ : X ⟶ Y} {f₂ : Y ⟶ S}
  {f₁' : X' ⟶ Y'} {f₂' : Y' ⟶ S'} {gX : X' ⟶ X} {gY : Y' ⟶ Y} {gS : S' ⟶ S}
variable (T : Compactification.Triangle f₁ f₂) (T' : Compactification.Triangle f₁' f₂')
  (ha : T'.cf.Z ⟶ T.cf.Z) (hb : T'.cg.Z ⟶ T.cg.Z) (hc : T'.cfg.Z ⟶ T.cfg.Z)
  (hfi : IsPullback gX T'.cf.i T.cf.i ha) (hfp : IsPullback ha T'.cf.g T.cf.g gY)
  (hgi : IsPullback gY T'.cg.i T.cg.i hb) (hgp : IsPullback hb T'.cg.g T.cg.g gS)
  (hci : IsPullback gX T'.cfg.i T.cfg.i hc)
  (hcp : IsPullback hc T'.cfg.g T.cfg.g gS)
  (hq : IsPullback ha T'.q T.q hc) (hp : hc ≫ T.p = T'.p ≫ hb)

-- The inverse of vertical open pasting, with the composition isomorphisms cancelled.
private lemma baseChange_open_comp_inv_app [F.HasBaseChange] (N : F.obj X) :
    haveI := HasBaseChange.isIso_baseChange (F := F) hfi
    haveI := HasBaseChange.isIso_baseChange (F := F) hci
    haveI := HasBaseChange.isIso_baseChange (F := F) hq
    inv ((F.baseChange ha T'.q T.q hc hq.w).natTrans.app ((F.sh T.cf.i).obj N)) ≫
      (F.sh T'.q).map (inv ((F.baseChange gX T'.cf.i T.cf.i ha hfi.w).natTrans.app N)) ≫
      (F.shComp' T'.cf.i T'.q T'.cfg.i T'.i_q).inv.app ((F.pb gX).obj N) =
    (F.pb hc).map ((F.shComp' T.cf.i T.q T.cfg.i T.i_q).inv.app N) ≫
      inv ((F.baseChange gX T'.cfg.i T.cfg.i hc hci.w).natTrans.app N) := by
  have := HasBaseChange.isIso_baseChange (F := F) hfi
  have := HasBaseChange.isIso_baseChange (F := F) hci
  have := HasBaseChange.isIso_baseChange (F := F) hq
  have h := congr_app (F.baseChange_paste_vert gX ha hc T'.cf.i T.cf.i T'.q T.q
    T'.cfg.i T.cfg.i hfi.w hq.w T'.i_q T.i_q hci.w) N
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Functor.comp_obj] at h
  have hi := (IsIso.inv_eq_inv (f := _) (g := _)).mpr h
  simp only [IsIso.inv_comp, Category.assoc, ← Functor.map_inv,
    NatIso.inv_inv_app, NatIso.inv_hom_app] at hi
  rw [hi]
  simp

-- Interchange and the open/proper pasting laws respect triangle composition.
include hq hp in
private lemma shriekBaseChange_compIso [F.HasProperExchange] :
    Functor.whiskerRight (F.compIso T).hom (F.pb gS) ≫
      (F.shriekBaseChange T.cfg T'.cfg hc hci hcp).natTrans =
    (F.shriekBaseChange T.cf T'.cf ha hfi hfp ≫ₕ
      F.shriekBaseChange T.cg T'.cg hb hgi hgp).natTrans ≫
      Functor.whiskerLeft (F.pb gX) (F.compIso T').hom := by
  have := HasBaseChange.isIso_baseChange (F := F) hfi
  have := HasBaseChange.isIso_baseChange (F := F) hgi
  have := HasBaseChange.isIso_baseChange (F := F) hci
  have := HasBaseChange.isIso_baseChange (F := F) hq
  have := HasBaseChange.isIso_baseChange (F := F) T.isPullback
  have := HasBaseChange.isIso_baseChange (F := F) T'.isPullback
  have hP := F.pfBaseChange_paste_vert hc hb gS T'.p T.p T'.cg.g T.cg.g
    T'.cfg.g T.cfg.g hp hgp.w T'.p_g T.p_g hcp.w
  have hinner (N : F.obj X) :
      (F.pb hb).map ((F.exchange T.cf.g T.q T.cg.i T.p T.isPullback.w).natTrans.app
          ((F.sh T.cf.i).obj N) ≫
        (F.pf T.p).map ((F.shComp' T.cf.i T.q T.cfg.i T.i_q).inv.app N)) ≫
        (F.pfBaseChange hc T'.p T.p hb hp).natTrans.app ((F.sh T.cfg.i).obj N) ≫
        (F.pf T'.p).map (inv ((F.baseChange gX T'.cfg.i T.cfg.i hc hci.w).natTrans.app N)) =
      inv ((F.baseChange gY T'.cg.i T.cg.i hb hgi.w).natTrans.app
        ((F.pf T.cf.g).obj ((F.sh T.cf.i).obj N))) ≫
        (F.sh T'.cg.i).map ((F.pfBaseChange ha T'.cf.g T.cf.g gY hfp.w).natTrans.app
          ((F.sh T.cf.i).obj N) ≫
          (F.pf T'.cf.g).map (inv
            ((F.baseChange gX T'.cf.i T.cf.i ha hfi.w).natTrans.app N))) ≫
        (F.exchange T'.cf.g T'.q T'.cg.i T'.p T'.isPullback.w).natTrans.app
          ((F.sh T'.cf.i).obj ((F.pb gX).obj N)) ≫
        (F.pf T'.p).map ((F.shComp' T'.cf.i T'.q T'.cfg.i T'.i_q).inv.app
          ((F.pb gX).obj N)) := by
    have hn := (F.pfBaseChange hc T'.p T.p hb hp).natTrans.naturality
      ((F.shComp' T.cf.i T.q T.cfg.i T.i_q).inv.app N)
    simp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [Functor.map_comp, Category.assoc]
    erw [reassoc_of% hn]
    rw [← Functor.map_comp]
    erw [← baseChange_open_comp_inv_app F T T' ha hc hfi hci hq N]
    simp only [Functor.map_comp, Category.assoc]
    have hh := exchange_cube_app F T.cf.g T.q T.cg.i T.p T'.cf.g T'.q T'.cg.i T'.p
      ha gY hc hb T.isPullback T'.isPullback hq hgi hfp.w hp ((F.sh T.cf.i).obj N)
    erw [reassoc_of% hh]
    have hnE := (F.exchange T'.cf.g T'.q T'.cg.i T'.p T'.isPullback.w).natTrans.naturality
      (inv ((F.baseChange gX T'.cf.i T.cf.i ha hfi.w).natTrans.app N))
    simp only [Functor.comp_map, Functor.comp_obj] at hnE
    erw [← reassoc_of% hnE]
  ext N
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, F.compIso_hom_app T N,
    F.compIso_hom_app T' ((F.pb gX).obj N)]
  simp only [shriekBaseChange, hP, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    TwoSquare.hComp, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj, Functor.map_comp, Category.assoc, NatIso.isIso_inv_app]
  dsimp only [shriek, Functor.comp_map, Functor.comp_obj]
  erw [Category.id_comp, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have hcancel :
      (F.pb gS).map ((F.pfComp' T.p T.cg.g T.cfg.g T.p_g).inv.app ((F.sh T.cfg.i).obj N)) ≫
        (F.pb gS).map ((F.pfComp' T.p T.cg.g T.cfg.g T.p_g).hom.app
          ((F.sh T.cfg.i).obj N)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app]
    exact (F.pb gS).map_id _
  erw [reassoc_of% hcancel]
  have hnP := (F.pfComp' T'.p T'.cg.g T'.cfg.g T'.p_g).inv.naturality
    (inv ((F.baseChange gX T'.cfg.i T.cfg.i hc hci.w).natTrans.app N))
  simp only [Functor.comp_map, Functor.comp_obj] at hnP
  erw [← hnP]
  have hnC := (F.pfBaseChange hb T'.cg.g T.cg.g gS hgp.w).natTrans.naturality
    ((F.exchange T.cf.g T.q T.cg.i T.p T.isPullback.w).natTrans.app
        ((F.sh T.cf.i).obj N) ≫
      (F.pf T.p).map ((F.shComp' T.cf.i T.q T.cfg.i T.i_q).inv.app N))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.map_comp, Category.assoc] at hnC
  erw [reassoc_of% hnC]
  have hi := congrArg (F.pf T'.cg.g).map (hinner N)
  simp only [Functor.map_comp, Category.assoc] at hi
  erw [reassoc_of% hi]
end TriangleBaseChange

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
  have hcomp (a b : Compactification f) (r : a.Refinement b)
      (hr : IsPullback a.i (𝟙 X) r.hom b.i) :
      (F.shriekBaseChangeOfIsPullback sq b).natTrans ≫
          Functor.whiskerLeft (F.pb g')
            (F.shriekIso (b.ofIsPullback sq) (HasCompactification.compactification f')).hom =
        Functor.whiskerRight (F.shriekIso b a).hom (F.pb g) ≫
          (F.shriekBaseChangeOfIsPullback sq a).natTrans ≫
          Functor.whiskerLeft (F.pb g')
            (F.shriekIso (a.ofIsPullback sq) (HasCompactification.compactification f')).hom := by
    let r' : (a.ofIsPullback sq).Refinement (b.ofIsPullback sq) :=
      { hom := pullback.lift (pullback.fst a.g g ≫ r.hom) (pullback.snd a.g g)
          (by rw [Category.assoc, r.hom_g, pullback.condition])
        i_hom := by
          apply pullback.hom_ext
          · rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
              a.ofIsPullback_i_fst sq, Category.assoc, r.i_hom,
              b.ofIsPullback_i_fst sq]
          · rw [Category.assoc, pullback.lift_snd, a.ofIsPullback_i_snd sq,
              b.ofIsPullback_i_snd sq]
        hom_g := pullback.lift_snd _ _ _ }
    have hcomm : pullback.fst a.g g ≫ r.hom = r'.hom ≫ pullback.fst b.g g :=
      (pullback.lift_fst _ _ _).symm
    have hbig : IsPullback g' (a.ofIsPullback sq).i b.i
        (r'.hom ≫ pullback.fst b.g g) := by
      simpa only [Category.comp_id, hcomm] using
        (a.isPullback_i_ofIsPullback sq).paste_horiz hr.flip
    have hr' : IsPullback (a.ofIsPullback sq).i (𝟙 X') r'.hom (b.ofIsPullback sq).i := by
      exact (IsPullback.of_right (h₁₁ := 𝟙 X') (by simpa using hbig)
        ((Category.id_comp _).trans r'.i_hom.symm) (b.isPullback_i_ofIsPullback sq)).flip
    have h := F.shriekBaseChange_refinementComparison r hr r' hr'
      (pullback.fst a.g g) (a.isPullback_i_ofIsPullback sq)
      (a.isPullback_g_ofIsPullback sq).flip (pullback.fst b.g g)
      (b.isPullback_i_ofIsPullback sq) (b.isPullback_g_ofIsPullback sq).flip hcomm
    have heq : (F.shriekIso b a).hom = F.refinementComparison r hr := by
      rw [← F.shriekIso_symm a b, F.shriekIso_eq_symm r hr]
      rfl
    rw [heq]
    rw [← Category.assoc, h, Category.assoc, ← Functor.whiskerLeft_comp]
    congr 1
    congr 1
    have heq' : F.refinementComparison r' hr' =
        (F.shriekIso (b.ofIsPullback sq) (a.ofIsPullback sq)).hom := by
      rw [← F.shriekIso_symm (a.ofIsPullback sq) (b.ofIsPullback sq),
        F.shriekIso_eq_symm r' hr']
      rfl
    rw [heq', ← Iso.trans_hom, F.shriekIso_trans]
  let d := HasCompactification.compactification f
  let e := Compactification.inf d c
  have h₁ := hcomp e d (Compactification.infFst d c)
    (Compactification.isPullback_infFst d c)
  have h₂ := hcomp e c (Compactification.infSnd d c)
    (Compactification.isPullback_infSnd d c)
  have h : (F.shriekBaseChangeOfIsPullback sq d).natTrans ≫
      Functor.whiskerLeft (F.pb g')
        (F.shriekIso (d.ofIsPullback sq) (HasCompactification.compactification f')).hom =
      Functor.whiskerRight (F.shriekIso d c).hom (F.pb g) ≫
        (F.shriekBaseChangeOfIsPullback sq c).natTrans ≫
        Functor.whiskerLeft (F.pb g')
          (F.shriekIso (c.ofIsPullback sq) (HasCompactification.compactification f')).hom := by
    rw [h₁, ← Category.assoc, h₂]
    simp only [← Category.assoc, ← Functor.whiskerRight_comp, ← Iso.trans_hom,
      F.shriekIso_trans]
  ext K
  simpa only [lowerShriekBaseChange, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Category.assoc] using congr_app h K

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
  have : QuasiCompact f₁ := .of_comp f₁ f₂
  let T := Compactification.Triangle.ofHasCompactification f₁ f₂
  let a := T.cf.ofIsPullback sq₁
  let b := T.cg.ofIsPullback sq₂
  let c := T.cfg.ofIsPullback sq
  let ha := pullback.fst T.cf.g gY
  let hb := pullback.fst T.cg.g gS
  let hc := pullback.fst T.cfg.g gS
  let p : c.Z ⟶ b.Z := pullback.lift (hc ≫ T.p) c.g
    (by rw [Category.assoc, T.p_g]; exact pullback.condition)
  have hp : p ≫ hb = hc ≫ T.p := pullback.lift_fst _ _ _
  have hpg : p ≫ b.g = c.g := pullback.lift_snd _ _ _
  let q : a.Z ⟶ c.Z := pullback.lift (ha ≫ T.q) (a.g ≫ f₂') (by
    rw [Category.assoc, ← T.p_g, ← Category.assoc T.q, ← T.isPullback.w,
      Category.assoc, ← Category.assoc ha, ← (T.cf.isPullback_g_ofIsPullback sq₁).w,
      Category.assoc, ← T.cg.comm, sq₂.w, Category.assoc])
  have hq : q ≫ hc = ha ≫ T.q := pullback.lift_fst _ _ _
  have hqg : q ≫ c.g = a.g ≫ f₂' := pullback.lift_snd _ _ _
  have hcomm : a.g ≫ b.i = q ≫ p := by
    apply pullback.hom_ext
    · change (a.g ≫ b.i) ≫ hb = (q ≫ p) ≫ hb
      rw [Category.assoc, ← (T.cg.isPullback_i_ofIsPullback sq₂).w,
        ← Category.assoc, ← (T.cf.isPullback_g_ofIsPullback sq₁).flip.w,
        Category.assoc, T.isPullback.w, ← Category.assoc, ← hq, Category.assoc, ← hp,
        ← Category.assoc]
    · change (a.g ≫ b.i) ≫ b.g = (q ≫ p) ≫ b.g
      rw [Category.assoc, ← b.comm, Category.assoc, hpg, hqg]
  have hpp : IsPullback hc p T.p hb := by
    apply IsPullback.of_bot (v₂₁ := b.g) (v₂₂ := T.cg.g) _ hp.symm
      (T.cg.isPullback_g_ofIsPullback sq₂).flip
    rw [hpg, T.p_g]
    exact (T.cfg.isPullback_g_ofIsPullback sq).flip
  have ht : IsPullback a.g q b.i p := by
    apply IsPullback.of_bot (v₂₁ := hc) (v₂₂ := hb) _ hcomm hpp.flip
    rw [hq, ← (T.cg.isPullback_i_ofIsPullback sq₂).w]
    exact (T.cf.isPullback_g_ofIsPullback sq₁).paste_vert T.isPullback
  have hqq : IsPullback ha q T.q hc := by
    apply IsPullback.of_right (h₁₂ := T.cf.g) (h₂₂ := T.p) _ hq.symm T.isPullback
    rw [(T.cf.isPullback_g_ofIsPullback sq₁).flip.w, ← hp]
    exact ht.paste_horiz (T.cg.isPullback_i_ofIsPullback sq₂)
  have : IsOpenImmersion q := MorphismProperty.IsStableUnderBaseChange.of_isPullback hqq
    T.isOpenImmersion_q
  have hiq : a.i ≫ q = c.i := by
    apply pullback.hom_ext
    · change (a.i ≫ q) ≫ hc = c.i ≫ hc
      rw [Category.assoc, hq, ← Category.assoc,
        T.cf.ofIsPullback_i_fst sq₁, Category.assoc, T.i_q,
        T.cfg.ofIsPullback_i_fst sq]
    · change (a.i ≫ q) ≫ c.g = c.i ≫ c.g
      rw [Category.assoc, hqg, ← Category.assoc, ← a.comm, ← c.comm]
  let T' : Compactification.Triangle f₁' f₂' :=
    { cf := a, cg := b, cfg := c, p := p, q := q,
      i_q := hiq, p_g := hpg, isPullback := ht }
  have hT :
      Functor.whiskerRight (F.compIso T).hom (F.pb gS) ≫
        (F.shriekBaseChangeOfIsPullback sq T.cfg).natTrans =
      (F.shriekBaseChangeOfIsPullback sq₁ T.cf ≫ₕ
        F.shriekBaseChangeOfIsPullback sq₂ T.cg).natTrans ≫
        Functor.whiskerLeft (F.pb gX) (F.compIso T').hom := by
    exact F.shriekBaseChange_compIso T T' ha hb hc
      (T.cf.isPullback_i_ofIsPullback sq₁) (T.cf.isPullback_g_ofIsPullback sq₁).flip
      (T.cg.isPullback_i_ofIsPullback sq₂) (T.cg.isPullback_g_ofIsPullback sq₂).flip
      (T.cfg.isPullback_i_ofIsPullback sq) (T.cfg.isPullback_g_ofIsPullback sq).flip
      hqq hp.symm
  have hC : (F.lowerShriekCompIso f₁ f₂).hom =
      Functor.whiskerRight
        (F.shriekIso (HasCompactification.compactification f₁) T.cf).hom (F.shriek T.cg) ≫
        (F.compIso T).hom ≫
        (F.shriekIso T.cfg (HasCompactification.compactification (f₁ ≫ f₂))).hom := by
    simp only [lowerShriekCompIso, Iso.trans_hom, Functor.isoWhiskerRight_hom]
    rfl
  have hcanonical :
      Functor.whiskerRight (F.lowerShriekCompIso f₁ f₂).hom (F.pb gS) ≫
        (F.lowerShriekBaseChange sq).natTrans =
      (F.lowerShriekBaseChange sq₁ ≫ₕ F.lowerShriekBaseChange sq₂).natTrans ≫
        Functor.whiskerLeft (F.pb gX) (F.lowerShriekCompIso f₁' f₂').hom := by
    rw [hC, F.lowerShriekBaseChange_eq sq T.cfg,
      F.lowerShriekBaseChange_eq sq₁ T.cf, F.lowerShriekCompIso_hom_eq T']
    simp only [lowerShriekBaseChange]
    rw [← F.shriekIso_symm T.cfg
      (HasCompactification.compactification (f₁ ≫ f₂)),
      ← F.shriekIso_symm a (HasCompactification.compactification f₁'),
      ← F.shriekIso_symm b (HasCompactification.compactification f₂')]
    ext N
    simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
      NatTrans.comp_app, NatTrans.hcomp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Functor.comp_obj, Functor.map_comp,
      Category.assoc]
    simp only [Iso.symm_hom]
    have hcancel :
        (F.pb gS).map ((F.shriekIso T.cfg
          (HasCompactification.compactification (f₁ ≫ f₂))).hom.app N) ≫
        (F.pb gS).map ((F.shriekIso T.cfg
          (HasCompactification.compactification (f₁ ≫ f₂))).inv.app N) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.hom_inv_id_app]
      exact (F.pb gS).map_id _
    erw [reassoc_of% hcancel]
    have h := congr_app hT N
    simp only [NatTrans.comp_app, TwoSquare.hComp, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id] at h
    erw [reassoc_of% h]
    have hnG := (F.shriekIso b (HasCompactification.compactification f₂')).hom.naturality
      ((F.pb gY).map ((F.shriekIso (HasCompactification.compactification f₁) T.cf).hom.app N) ≫
        (F.shriekBaseChangeOfIsPullback sq₁ T.cf).natTrans.app N ≫
        (F.shriekIso a (HasCompactification.compactification f₁')).hom.app ((F.pb gX).obj N))
    simp only [Functor.map_comp, Category.assoc] at hnG
    erw [← reassoc_of% hnG, Iso.hom_inv_id_app_assoc]
    have hAcancel :
        (F.shriek b).map ((F.shriekIso a
          (HasCompactification.compactification f₁')).hom.app ((F.pb gX).obj N)) ≫
        (F.shriek b).map ((F.shriekIso a
          (HasCompactification.compactification f₁')).inv.app ((F.pb gX).obj N)) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.hom_inv_id_app]
      exact (F.shriek b).map_id _
    erw [reassoc_of% hAcancel]
    have hnB := (F.shriekBaseChangeOfIsPullback sq₂ T.cg).natTrans.naturality
      ((F.shriekIso (HasCompactification.compactification f₁) T.cf).hom.app N)
    simp only [Functor.comp_map, Functor.comp_obj] at hnB
    erw [reassoc_of% hnB]
    rfl
  ext N
  have h := congr_app hcanonical N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  rw [← cancel_epi ((F.pb gS).map ((F.lowerShriekCompIso f₁ f₂).hom.app N))]
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc]
  rw [← h, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  simp


end Canonical

end AlgebraicGeometry.CompactSupportFormalism
