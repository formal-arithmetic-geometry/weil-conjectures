/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.TraceFormula.PullbackFamily

/-!

# Base change for a family of pushforwards

Let `P` be a family of pullbacks `P f : D Y ⥤ D X` with composition isomorphisms
`c f g : P (f ≫ g) ≅ P g ⋙ P f` (`CategoryTheory.PullbackAssoc`), and `Q f : D X ⥤ D Y` right
adjoints `P f ⊣ Q f`. For a commutative square `g' ≫ f = f' ≫ g`, the base-change morphism
`Q f ⋙ P g ⟶ P g' ⋙ Q f'` (`CategoryTheory.pushforwardBaseChange`) is the exchange morphism of the
comparison `P g ⋙ P f' ≅ P f ⋙ P g'` of the composition isomorphisms
(`CategoryTheory.pullbackFamilySquareComparison`). This file proves:

- `CategoryTheory.pushforwardBaseChange_app_paste`: the pasting law of base-change morphisms of
  two horizontally adjacent squares;
- `CategoryTheory.Iso.powSuccStr_pushforwardBaseChange`: for `f : X ⟶ Y` with
  `e_X ≫ f = f ≫ e_Y`, the iterated structure isomorphism of the pushforward `Q f F` of an
  algebra `(F, φ)` for `P e_X` is the base change along `e_X^{n+1}`, `e_Y^{n+1}` followed by the
  pushforward of the iterated structure isomorphism of `F`;
- `Endofunctor.IsoAlgebra.nonempty_overPowSucc_mapOfNatIso_iso_of_eq`: the same as an isomorphism of
  algebras, for functors given through equations, so that it applies to the pushforward of Weil
  sheaves.

## Implementation notes

The statements are generic in the families `P` and `Q`. Instantiated directly for module objects on
the pro-étale sites, the elaborator and the kernel unfold the pullbacks while comparing terms that
are equal only up to unfolding (`WeilConjectures.TraceFormula.PullbackFamily`).

-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory.Adjunction

section ExchangeRight

variable {A B A' B' A'' B'' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Category* A''] [Category* B''] {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}
  {Lf'' : B'' ⥤ A''} {Rf'' : A'' ⥤ B''}

/-- The exchange morphism `exchangeRight af af' θ` is the mate of `θ.hom`. -/
lemma exchangeRight_eq_mateEquiv {G : B ⥤ B'} {G' : A ⥤ A'} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf')
    (θ : G ⋙ Lf' ≅ Lf ⋙ G') :
    exchangeRight af af' θ = (mateEquiv af af' (TwoSquare.mk _ _ _ _ θ.hom)).natTrans := by
  ext K
  rw [exchangeRight_app]
  simp [mateEquiv]

/-- The exchange morphism of a natural isomorphism is an isomorphism when the horizontal functors
are equivalences. -/
lemma isIso_exchangeRight_of_isEquivalence {G : B ⥤ B'} {G' : A ⥤ A'} [G.IsEquivalence]
    [G'.IsEquivalence] (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (θ : G ⋙ Lf' ≅ Lf ⋙ G') :
    IsIso (exchangeRight af af' θ) := by
  rw [exchangeRight_eq_mateEquiv]
  exact isIso_mateEquiv_of_isEquivalence af af' _

/-- **Pasting law of exchange morphisms.** Let `θ₁ : G₁ ⋙ Lf' ≅ Lf ⋙ G₁'` and
`θ₂ : G₂ ⋙ Lf'' ≅ Lf' ⋙ G₂'` be comparisons of two horizontally adjacent squares, and
`θ : G ⋙ Lf'' ≅ Lf ⋙ G'` one of the outer square, compatible with `θ₁` and `θ₂` through
isomorphisms `c : G ≅ G₁ ⋙ G₂` and `c' : G' ≅ G₁' ⋙ G₂'`. Then the exchange morphism of `θ` is
the pasting of those of `θ₁` and `θ₂`, through `c` and `c'`. The squares are
```
B --G₁--> B' --G₂--> B''
|Lf        |Lf'       |Lf''
v          v           v
A --G₁'-> A' --G₂'-> A''
```
with right adjoints `Rf`, `Rf'`, `Rf''` going up. -/
lemma exchangeRight_app_paste {G₁ : B ⥤ B'} {G₁' : A ⥤ A'} {G₂ : B' ⥤ B''} {G₂' : A' ⥤ A''}
    {G : B ⥤ B''} {G' : A ⥤ A''} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (af'' : Lf'' ⊣ Rf'')
    (θ₁ : G₁ ⋙ Lf' ≅ Lf ⋙ G₁') (θ₂ : G₂ ⋙ Lf'' ≅ Lf' ⋙ G₂') (θ : G ⋙ Lf'' ≅ Lf ⋙ G')
    (c : G ≅ G₁ ⋙ G₂) (c' : G' ≅ G₁' ⋙ G₂')
    (h : ∀ N : B, Lf''.map (c.hom.app N) ≫ θ₂.hom.app (G₁.obj N) ≫ G₂'.map (θ₁.hom.app N) =
      θ.hom.app N ≫ c'.hom.app (Lf.obj N)) (K : A) :
    c.hom.app (Rf.obj K) ≫ G₂.map ((exchangeRight af af' θ₁).app K) ≫
        (exchangeRight af' af'' θ₂).app (G₁'.obj K) =
      (exchangeRight af af'' θ).app K ≫ Rf''.map (c'.hom.app K) := by
  have h₁ : Lf'.map ((exchangeRight af af' θ₁).app K) ≫ af'.counit.app (G₁'.obj K) =
      θ₁.hom.app (Rf.obj K) ≫ G₁'.map (af.counit.app K) := by
    have h := (af'.homEquiv _ _).symm_apply_apply
      (θ₁.hom.app (Rf.obj K) ≫ G₁'.map (af.counit.app K))
    rw [homEquiv_counit, homEquiv_unit] at h
    rw [exchangeRight_app, ← Rf'.map_comp]
    exact h
  have hη := af''.unit.naturality
    (c.hom.app (Rf.obj K) ≫ G₂.map ((exchangeRight af af' θ₁).app K))
  have hθ := θ₂.hom.naturality ((exchangeRight af af' θ₁).app K)
  have hc := c'.hom.naturality (af.counit.app K)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hη hθ hc
  rw [exchangeRight_app af' af'' θ₂, exchangeRight_app af af'' θ, ← Category.assoc,
    ← Category.assoc, hη, Category.assoc, ← Rf''.map_comp, ← Rf''.map_comp, ← Rf''.map_comp,
    Lf''.map_comp, Category.assoc, reassoc_of% hθ, ← G₂'.map_comp, h₁, G₂'.map_comp,
    reassoc_of% h, ← hc]
  simp only [Functor.map_comp, Category.assoc]

end ExchangeRight

end CategoryTheory.Adjunction

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : C → Type*} [∀ X, Category (D X)]
  {P : ∀ {X Y : C}, (X ⟶ Y) → D Y ⥤ D X}
  {c : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f}
  {Q : ∀ {X Y : C}, (X ⟶ Y) → D X ⥤ D Y} (adj : ∀ {X Y : C} (f : X ⟶ Y), P f ⊣ Q f)

section BaseChange

variable {X Y X' Y' : C} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

variable (c) in
/-- The comparison `P g ⋙ P f' ≅ P f ⋙ P g'` of a commutative square `g' ≫ f = f' ≫ g`, through
the composition isomorphisms. -/
def pullbackFamilySquareComparison (h : g' ≫ f = f' ≫ g) : P g ⋙ P f' ≅ P f ⋙ P g' :=
  (c f' g).symm ≪≫ eqToIso (congrArg (fun x ↦ P x) h.symm) ≪≫ c g' f

lemma pullbackFamilySquareComparison_hom_app (h : g' ≫ f = f' ≫ g) (N : D Y) :
    (pullbackFamilySquareComparison c h).hom.app N =
      (c f' g).inv.app N ≫ eqToHom (by rw [h]) ≫ (c g' f).hom.app N := by
  simp [pullbackFamilySquareComparison, eqToHom_app]

variable (c) in
/-- The base-change morphism `Q f ⋙ P g ⟶ P g' ⋙ Q f'` of a commutative square
`g' ≫ f = f' ≫ g`: the exchange morphism of `pullbackFamilySquareComparison` under the
adjunctions `P f ⊣ Q f` and `P f' ⊣ Q f'`. -/
def pushforwardBaseChange (h : g' ≫ f = f' ≫ g) : Q f ⋙ P g ⟶ P g' ⋙ Q f' :=
  Adjunction.exchangeRight (adj f) (adj f') (pullbackFamilySquareComparison c h)

variable {X'' Y'' : C} {k : Y'' ⟶ Y'} {k' : X'' ⟶ X'} {f'' : X'' ⟶ Y''}

/-- **Pasting law of the pullback comparisons**: the comparison of the outer square of two
horizontally pasted squares is the pasting of their comparisons, through the composition
isomorphisms. The squares are
```
X'' --k'--> X' --g'--> X
 |f''       |f'        |f
 v          v          v
Y'' --k---> Y' --g---> Y
```
-/
lemma pullbackFamilySquareComparison_paste (hc : PullbackAssoc P c) (h₁ : g' ≫ f = f' ≫ g)
    (h₂ : k' ≫ f' = f'' ≫ k) (h : (k' ≫ g') ≫ f = f'' ≫ (k ≫ g)) (N : D Y) :
    (P f'').map ((c k g).hom.app N) ≫
        (pullbackFamilySquareComparison c h₂).hom.app ((P g).obj N) ≫
          (P k').map ((pullbackFamilySquareComparison c h₁).hom.app N) =
      (pullbackFamilySquareComparison c h).hom.app N ≫ (c k' g').hom.app ((P f).obj N) := by
  rw [← cancel_epi ((c f'' (k ≫ g)).hom.app N), pullbackFamilySquareComparison_hom_app,
    pullbackFamilySquareComparison_hom_app, pullbackFamilySquareComparison_hom_app]
  simp only [Category.assoc, Functor.map_comp, Iso.hom_inv_id_app_assoc]
  rw [hc.hom_app_comp_map_hom_app_assoc f'' k g, Iso.hom_inv_id_app_assoc,
    pullbackComp_hom_app_comp_eqToHom_left_assoc (c := c) h₂.symm g,
    reassoc_of% (hc.hom_app k' f' g N)]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, eqToHom_map,
    pullbackComp_hom_app_comp_eqToHom_right_assoc (c := c) k' h₁.symm,
    hc.hom_app_comp_map_hom_app k' g' f]
  simp only [eqToHom_trans_assoc]

/-- **Pasting law of the base-change morphisms**: the base-change morphism of the outer square of
two horizontally pasted squares is the pasting of their base-change morphisms, through the
composition isomorphisms. The squares are
```
X'' --k'--> X' --g'--> X
 |f''       |f'        |f
 v          v          v
Y'' --k---> Y' --g---> Y
```
-/
@[reassoc]
lemma pushforwardBaseChange_app_paste (hc : PullbackAssoc P c) (h₁ : g' ≫ f = f' ≫ g)
    (h₂ : k' ≫ f' = f'' ≫ k) (h : (k' ≫ g') ≫ f = f'' ≫ (k ≫ g)) (M : D X) :
    (c k g).hom.app ((Q f).obj M) ≫ (P k).map ((pushforwardBaseChange c adj h₁).app M) ≫
        (pushforwardBaseChange c adj h₂).app ((P g').obj M) =
      (pushforwardBaseChange c adj h).app M ≫ (Q f'').map ((c k' g').hom.app M) :=
  Adjunction.exchangeRight_app_paste (adj f) (adj f') (adj f'')
    (pullbackFamilySquareComparison c h₁) (pullbackFamilySquareComparison c h₂)
    (pullbackFamilySquareComparison c h) (c k g) (c k' g')
    (pullbackFamilySquareComparison_paste hc h₁ h₂ h) M

end BaseChange

section Over

variable {T : C}

/-- **The iterated structure isomorphism of a pushforward**: for `f : X ⟶ Y` over `T` with
`e_X ≫ f = f ≫ e_Y` and an algebra `(F, φ)` for `P e_X`, the iterated structure isomorphism of the
pushforward `Q f F` with `P e_Y (Q f F) ⟶ Q f (P e_X F) ⟶ Q f F` (base change followed by
`Q f φ`) is the base change along `e_X^{n+1}`, `e_Y^{n+1}` followed by the pushforward of the
iterated structure isomorphism of `F`. -/
theorem Iso.powSuccStr_pushforwardBaseChange (hc : PullbackAssoc P c) {X Y : Over T}
    (eX : X ≅ X) (eY : Y ≅ Y) (f : X ⟶ Y) (hf : eX.hom ≫ f = f ≫ eY.hom) {F : D X.left}
    (φ : (P eX.hom.left).obj F ≅ F) (ψ : (P eY.hom.left).obj ((Q f.left).obj F) ≅ (Q f.left).obj F)
    (hψ : ψ.hom = (pushforwardBaseChange c adj (Over.left_comp_left_eq_of_comp_eq hf)).app F ≫
      (Q f.left).map φ.hom) (n : ℕ) :
    (eY.powSuccStr (fun g ↦ P g.left) (fun a b ↦ c a.left b.left) ψ n).hom =
      (pushforwardBaseChange c adj (Over.left_comp_left_eq_of_comp_eq
          (Iso.powSucc_hom_comp_eq_comp_powSucc_hom eX eY hf n))).app F ≫
        (Q f.left).map (eX.powSuccStr (fun g ↦ P g.left) (fun a b ↦ c a.left b.left) φ n).hom := by
  induction n with
  | zero => exact hψ
  | succ n ih =>
    have hn := Over.left_comp_left_eq_of_comp_eq
      (Iso.powSucc_hom_comp_eq_comp_powSucc_hom eX eY hf n)
    have hf' := Over.left_comp_left_eq_of_comp_eq hf
    have nat := (pushforwardBaseChange c adj hn).naturality φ.hom
    simp only [Functor.comp_map] at nat
    change (c (eY.powSucc n).hom.left eY.hom.left).hom.app ((Q f.left).obj F) ≫
        (P (eY.powSucc n).hom.left).map ψ.hom ≫
        (eY.powSuccStr (fun g ↦ P g.left) (fun a b ↦ c a.left b.left) ψ n).hom =
      (pushforwardBaseChange c adj (show ((eX.powSucc n).hom.left ≫ eX.hom.left) ≫ f.left =
          f.left ≫ ((eY.powSucc n).hom.left ≫ eY.hom.left)
          by rw [Category.assoc, hf', ← Category.assoc, hn, Category.assoc])).app F ≫
        (Q f.left).map ((c (eX.powSucc n).hom.left eX.hom.left).hom.app F ≫
          (P (eX.powSucc n).hom.left).map φ.hom ≫
          (eX.powSuccStr (fun g ↦ P g.left) (fun a b ↦ c a.left b.left) φ n).hom)
    rw [ih, hψ, Functor.map_comp_assoc, reassoc_of% nat, Functor.map_comp, Functor.map_comp,
      ← pushforwardBaseChange_app_paste_assoc adj hc hf' hn]

/-- **The pushforward commutes with the iterated structures**, as an isomorphism of algebras:
for `f : X ⟶ Y` over `T` with `e_X ≫ f = f ≫ e_Y`, comparisons `β : Q f ⋙ P e_Y ≅ P e_X ⋙ Q f`
and `βₙ : Q f ⋙ P e_Y^{n+1} ≅ P e_X^{n+1} ⋙ Q f` given by the base-change morphisms, and an
algebra `F` for `P e_X`, the `(n + 1)`-st iterate of the transport of `F` along `β` is the
transport along `βₙ` of the `(n + 1)`-st iterate of `F`. The functors are given through
equations, so that concrete instances can use their own functors.

Implementation note: the categories are passed as variables, with their category instances,
together with `Sigma`-type equations to the generic ones, and the functors through `HEq`
hypotheses, as in `Endofunctor.IsoAlgebra.nonempty_obj_obj_iso_of_eq`. -/
theorem Endofunctor.IsoAlgebra.nonempty_overPowSucc_mapOfNatIso_iso_of_eq
    (hc : PullbackAssoc P c) {X Y : Over T} (eX : X ≅ X) (eY : Y ≅ Y) (f : X ⟶ Y)
    (hf : eX.hom ≫ f = f ≫ eY.hom) (n : ℕ)
    (β : Q f.left ⋙ P eY.hom.left ≅ P eX.hom.left ⋙ Q f.left)
    (hβ : β.hom = pushforwardBaseChange c adj (Over.left_comp_left_eq_of_comp_eq hf))
    (βn : Q f.left ⋙ P (eY.powSucc n).hom.left ≅ P (eX.powSucc n).hom.left ⋙ Q f.left)
    (hβn : βn.hom = pushforwardBaseChange c adj (Over.left_comp_left_eq_of_comp_eq
      (Iso.powSucc_hom_comp_eq_comp_powSucc_hom eX eY hf n)))
    (𝒜X 𝒜Y 𝒜Xn 𝒜Yn : Type _) {i𝒜X : Category 𝒜X} {i𝒜Y : Category 𝒜Y} {i𝒜Xn : Category 𝒜Xn}
    {i𝒜Yn : Category 𝒜Yn} (F : 𝒜X) (Λ₁ : 𝒜X ⥤ 𝒜Y) (Λn : 𝒜Xn ⥤ 𝒜Yn) (TX : 𝒜X ⥤ 𝒜Xn)
    (TY : 𝒜Y ⥤ 𝒜Yn)
    (h𝒜X : (⟨𝒜X, i𝒜X⟩ : Σ A : Type _, Category A) =
      ⟨Endofunctor.IsoAlgebra (P eX.hom.left), inferInstance⟩)
    (h𝒜Y : (⟨𝒜Y, i𝒜Y⟩ : Σ A : Type _, Category A) =
      ⟨Endofunctor.IsoAlgebra (P eY.hom.left), inferInstance⟩)
    (h𝒜Xn : (⟨𝒜Xn, i𝒜Xn⟩ : Σ A : Type _, Category A) =
      ⟨Endofunctor.IsoAlgebra (P (eX.powSucc n).hom.left), inferInstance⟩)
    (h𝒜Yn : (⟨𝒜Yn, i𝒜Yn⟩ : Σ A : Type _, Category A) =
      ⟨Endofunctor.IsoAlgebra (P (eY.powSucc n).hom.left), inferInstance⟩)
    (hΛ₁ : HEq Λ₁ (Endofunctor.IsoAlgebra.mapOfNatIso β))
    (hΛn : HEq Λn (Endofunctor.IsoAlgebra.mapOfNatIso βn))
    (hTX : HEq TX (Endofunctor.IsoAlgebra.overPowSuccFunctor c eX n))
    (hTY : HEq TY (Endofunctor.IsoAlgebra.overPowSuccFunctor c eY n)) :
    Nonempty (TY.obj (Λ₁.obj F) ≅ Λn.obj (TX.obj F)) := by
  cases h𝒜X
  cases h𝒜Y
  cases h𝒜Xn
  cases h𝒜Yn
  cases hΛ₁
  cases hΛn
  cases hTX
  cases hTY
  refine ⟨Endofunctor.IsoAlgebra.isoMk (Iso.refl _) ?_⟩
  change (P (eY.powSucc n).hom.left).map (𝟙 _) ≫
      (βn.hom.app F.carrier ≫ (Q f.left).map
        (eX.powSuccStr (fun g ↦ P g.left) (fun a b ↦ c a.left b.left) F.str n).hom) =
    (eY.powSuccStr (fun g ↦ P g.left) (fun a b ↦ c a.left b.left)
      ((Endofunctor.IsoAlgebra.mapOfNatIso β).obj F).str n).hom ≫ 𝟙 _
  rw [Functor.map_id, Category.id_comp, Category.comp_id, hβn,
    Iso.powSuccStr_pushforwardBaseChange adj hc eX eY f hf F.str _
      (by rw [Endofunctor.IsoAlgebra.mapOfNatIso_obj_str, Iso.trans_hom, Iso.app_hom, hβ,
        Functor.mapIso_hom]) n]

end Over

end CategoryTheory
