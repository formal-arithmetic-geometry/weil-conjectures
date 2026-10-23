/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ShriekTraceFunction

/-!

# Coherence of pullbacks along intertwining morphisms

Let `P` be a family of functors `P f : D Y ⥤ D X`, indexed by the morphisms `f : X ⟶ Y` of a
category `C`, contravariant up to composition isomorphisms `c f g : P (f ≫ g) ≅ P g ⋙ P f`
satisfying the associativity law (a pseudofunctor `Cᵒᵖ ⥤ Cat`, without unit). The pullbacks of
module objects on the pro-étale sites (`ProEtale.CondensedRing.upperStar`, with
`ProEtale.CondensedRing.upperStarComp`) are such a family.

For a morphism `g : W ⟶ X` intertwining endomorphisms `e_W` and `e_X` (`e_W ≫ g = g ≫ e_X`), an
object `F` of `D X` with an isomorphism `φ : P e_X F ≅ F` is sent to `P g F` with the isomorphism
`P e_W (P g F) ≅ P g (P e_X F) ≅ P g F` given by the comparison `pullbackComparison` and
`P g φ`. This file proves the two coherences behind the pullback of Weil sheaves:

- `CategoryTheory.Iso.powSuccStr_pullbackComparison`: the iterated structure isomorphism of the
  pullback is the pullback of the iterated structure isomorphism, along `e_W^{n+1}`, `e_X^{n+1}`;
- `CategoryTheory.pullbackComparison_stalkComparison`: for a point `w : S ⟶ W` fixed by `e_W` up
  to an endomorphism `s` of `S` with `τ : P s ≅ 𝟭`, the composition isomorphism
  `P (w ≫ g) F ≅ P w (P g F)` intertwines the two stalk structures.

-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory.Over

/-- An equation `a ≫ b = c ≫ d` in `Over T` holds for the underlying morphisms. -/
lemma left_comp_left_eq_of_comp_eq {S : Type*} [Category S] {T : S} {A B C D : Over T}
    {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C} {d : C ⟶ D} (h : a ≫ b = c ≫ d) :
    a.left ≫ b.left = c.left ≫ d.left := by
  rw [← Over.comp_left, h, Over.comp_left]

end CategoryTheory.Over

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : C → Type*} [∀ X, Category (D X)]
  (P : ∀ {X Y : C}, (X ⟶ Y) → D Y ⥤ D X)
  (c : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)

/-- The associativity law of the composition isomorphisms `c f g : P (f ≫ g) ≅ P g ⋙ P f` of a
family of pullbacks. -/
def PullbackAssoc : Prop :=
  ∀ {X Y Z V : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V),
    c f (g ≫ h) ≪≫ Functor.isoWhiskerRight (c g h) (P f) ≪≫ (P h).associator (P g) (P f) =
      eqToIso (congrArg (fun x ↦ P x) (Category.assoc f g h).symm) ≪≫ c (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (P h) (c f g)

variable {P c}

/-- The associativity law of a family of pullbacks, at an object. -/
lemma PullbackAssoc.hom_app (hc : PullbackAssoc P c) {X Y Z V : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ V) (M : D V) :
    (c (f ≫ g) h).hom.app M ≫ (c f g).hom.app ((P h).obj M) =
      eqToHom (by rw [Category.assoc]) ≫ (c f (g ≫ h)).hom.app M ≫
        (P f).map ((c g h).hom.app M) := by
  have := congrArg (fun e ↦ e.hom.app M) (hc f g h)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.comp_id, eqToIso.hom, eqToHom_app] at this
  rw [this, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The associativity law, solved for `c f (g ≫ h)` followed by `P f (c g h)`. -/
@[reassoc]
lemma PullbackAssoc.hom_app_comp_map_hom_app (hc : PullbackAssoc P c) {X Y Z V : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : Z ⟶ V) (M : D V) :
    (c f (g ≫ h)).hom.app M ≫ (P f).map ((c g h).hom.app M) =
      eqToHom (by rw [Category.assoc]) ≫ (c (f ≫ g) h).hom.app M ≫
        (c f g).hom.app ((P h).obj M) := by
  rw [hc.hom_app f g h M, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

section Transport

variable {X Y Z : C}

include c in
/-- Transport of the composition isomorphism along an equation of its first morphism. -/
@[reassoc]
lemma pullbackComp_hom_app_comp_eqToHom_left {f f' : X ⟶ Y} (h : f = f') (g : Y ⟶ Z)
    (M : D Z) :
    (c f g).hom.app M ≫ eqToHom (by rw [h]) =
      eqToHom (by rw [h]) ≫ (c f' g).hom.app M := by
  subst h
  simp

include c in
/-- Transport of the composition isomorphism along an equation of its second morphism. -/
@[reassoc]
lemma pullbackComp_hom_app_comp_eqToHom_right {g g' : Y ⟶ Z} (f : X ⟶ Y) (h : g = g')
    (M : D Z) :
    (c f g).hom.app M ≫ eqToHom (by rw [h]) =
      eqToHom (by rw [h]) ≫ (c f g').hom.app M := by
  subst h
  simp

/-- Transport of the image of a morphism along an equation of morphisms. -/
@[reassoc]
lemma map_comp_eqToHom_of_eq {f f' : X ⟶ Y} (h : f = f') {M N : D Y} (u : M ⟶ N) :
    (P f).map u ≫ eqToHom (by rw [h]) = eqToHom (by rw [h]) ≫ (P f').map u := by
  subst h
  simp

end Transport

/-- The comparison `P g ⋙ P e_W ≅ P e_X ⋙ P g` for a morphism `g : W ⟶ X` with
`e_W ≫ g = g ≫ e_X`: the composite of the composition isomorphisms and the transport along
`e_W ≫ g = g ≫ e_X`. -/
def pullbackComparison {W X : C} (g : W ⟶ X) (eW : W ⟶ W) (eX : X ⟶ X)
    (hg : eW ≫ g = g ≫ eX) : P g ⋙ P eW ≅ P eX ⋙ P g :=
  (c eW g).symm ≪≫ eqToIso (congrArg (fun f ↦ P f) hg) ≪≫ c g eX

lemma pullbackComparison_hom_app {W X : C} (g : W ⟶ X) (eW : W ⟶ W) (eX : X ⟶ X)
    (hg : eW ≫ g = g ≫ eX) (M : D X) :
    (pullbackComparison (c := c) g eW eX hg).hom.app M =
      (c eW g).inv.app M ≫ eqToHom (by rw [hg]) ≫ (c g eX).hom.app M := by
  simp [pullbackComparison, eqToHom_app]

/-- The key identity behind `Iso.powSuccStr_pullbackComparison`: for `E ≫ g = g ≫ E'` and
`e ≫ g = g ≫ e'`, the two ways of identifying `P (E ≫ e) (P g F)` with
`P g (P E' (P e' F))` agree. -/
@[reassoc]
lemma pullbackComparison_comp_aux (hc : PullbackAssoc P c) {W X : C} (g : W ⟶ X)
    (E e : W ⟶ W) (E' e' : X ⟶ X) (hE : E ≫ g = g ≫ E') (he : e ≫ g = g ≫ e') (F : D X) :
    (c E e).hom.app ((P g).obj F) ≫ (P E).map ((c e g).inv.app F) ≫
        (P E).map (eqToHom (by rw [he])) ≫ (P E).map ((c g e').hom.app F) ≫
        (c E g).inv.app ((P e').obj F) ≫ eqToHom (by rw [hE]) ≫
        (c g E').hom.app ((P e').obj F) =
      (c (E ≫ e) g).inv.app F ≫
        eqToHom (by rw [Category.assoc, he, ← Category.assoc, hE, Category.assoc]) ≫
        (c g (E' ≫ e')).hom.app F ≫ (P g).map ((c E' e').hom.app F) := by
  rw [← cancel_epi ((c (E ≫ e) g).hom.app F), Iso.hom_inv_id_app_assoc,
    reassoc_of% (hc.hom_app E e g F), ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id,
    Category.id_comp, eqToHom_map, pullbackComp_hom_app_comp_eqToHom_right_assoc (c := c) E he,
    hc.hom_app_comp_map_hom_app_assoc, Iso.hom_inv_id_app_assoc,
    pullbackComp_hom_app_comp_eqToHom_left_assoc (c := c) hE,
    hc.hom_app_comp_map_hom_app]
  simp only [eqToHom_trans_assoc]

/-- **The iterated structure isomorphism of a pullback**: for `g : W ⟶ X` with
`e_W ≫ g = g ≫ e_X` and `φ : P e_X F ≅ F`, the iterated structure isomorphism of `P g F` with
`P e_W (P g F) ≅ P g (P e_X F) ≅ P g F` is the pullback, along `e_W^{n+1}` and `e_X^{n+1}`, of
the iterated structure isomorphism of `F`. -/
theorem Iso.powSuccStr_pullbackComparison (hc : PullbackAssoc P c) {W X : C} (eW : W ≅ W)
    (eX : X ≅ X) (g : W ⟶ X) (hg : eW.hom ≫ g = g ≫ eX.hom) {F : D X}
    (φ : (P eX.hom).obj F ≅ F) (n : ℕ) :
    (eW.powSuccStr (fun f ↦ P f) (fun f f' ↦ c f f')
        ((pullbackComparison (c := c) g eW.hom eX.hom hg).app F ≪≫ (P g).mapIso φ) n).hom =
      (pullbackComparison (c := c) g (eW.powSucc n).hom (eX.powSucc n).hom
          (Iso.powSucc_hom_comp_eq_comp_powSucc_hom eW eX hg n)).hom.app F ≫
        (P g).map (eX.powSuccStr (fun f ↦ P f) (fun f f' ↦ c f f') φ n).hom := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := Iso.powSucc_hom_comp_eq_comp_powSucc_hom eW eX hg n
    change (c (eW.powSucc n).hom eW.hom).hom.app ((P g).obj F) ≫
        (P (eW.powSucc n).hom).map
          ((pullbackComparison (c := c) g eW.hom eX.hom hg).hom.app F ≫ (P g).map φ.hom) ≫
        (eW.powSuccStr (fun f ↦ P f) (fun f f' ↦ c f f')
          ((pullbackComparison (c := c) g eW.hom eX.hom hg).app F ≪≫ (P g).mapIso φ) n).hom =
      (pullbackComparison (c := c) g ((eW.powSucc n).hom ≫ eW.hom)
          ((eX.powSucc n).hom ≫ eX.hom)
          (by rw [Category.assoc, hg, ← Category.assoc, hn, Category.assoc])).hom.app F ≫
        (P g).map ((c (eX.powSucc n).hom eX.hom).hom.app F ≫
          (P (eX.powSucc n).hom).map φ.hom ≫
          (eX.powSuccStr (fun f ↦ P f) (fun f f' ↦ c f f') φ n).hom)
    rw [ih]
    simp only [pullbackComparison_hom_app, Functor.map_comp, Category.assoc]
    have nat₁ := (c (eW.powSucc n).hom g).inv.naturality φ.hom
    have nat₂ := (c g (eX.powSucc n).hom).hom.naturality φ.hom
    simp only [Functor.comp_map] at nat₁ nat₂
    rw [reassoc_of% nat₁, map_comp_eqToHom_of_eq_assoc hn, reassoc_of% nat₂,
      pullbackComparison_comp_aux_assoc hc g _ _ _ _ hn hg F]

/-- A version of `Iso.powSuccStr_pullbackComparison` for a structure isomorphism `ψ` of `P g F` given
through its underlying morphism. -/
theorem Iso.powSuccStr_hom_eq_of_hom_eq (hc : PullbackAssoc P c) {W X : C} (eW : W ≅ W)
    (eX : X ≅ X) (g : W ⟶ X) (hg : eW.hom ≫ g = g ≫ eX.hom) {F : D X}
    (φ : (P eX.hom).obj F ≅ F) (ψ : (P eW.hom).obj ((P g).obj F) ≅ (P g).obj F)
    (hψ : ψ.hom = (pullbackComparison (c := c) g eW.hom eX.hom hg).hom.app F ≫ (P g).map φ.hom)
    (n : ℕ) :
    (eW.powSuccStr (fun f ↦ P f) (fun f f' ↦ c f f') ψ n).hom =
      (pullbackComparison (c := c) g (eW.powSucc n).hom (eX.powSucc n).hom
          (Iso.powSucc_hom_comp_eq_comp_powSucc_hom eW eX hg n)).hom.app F ≫
        (P g).map (eX.powSuccStr (fun f ↦ P f) (fun f f' ↦ c f f') φ n).hom := by
  obtain rfl : ψ = (pullbackComparison (c := c) g eW.hom eX.hom hg).app F ≪≫ (P g).mapIso φ :=
    Iso.ext hψ
  exact Iso.powSuccStr_pullbackComparison hc eW eX g hg φ n

section Stalk

variable {S : C} {s : S ⟶ S}

/-- The stalk comparison `P x ≅ P e ⋙ P x` at a point `x : S ⟶ V` fixed by `e : V ⟶ V` up to an
endomorphism `s` of `S` with `τ : P s ≅ 𝟭` (`x ≫ e = s ≫ x`): the composite
`P x ≅ P x ⋙ P s ≅ P (s ≫ x) = P (x ≫ e) ≅ P e ⋙ P x`. -/
def stalkComparison (τ : P s ≅ 𝟭 (D S)) {V : C} (x : S ⟶ V) (e : V ⟶ V) (h : x ≫ e = s ≫ x) :
    P x ⋙ 𝟭 (D S) ≅ P e ⋙ P x :=
  Functor.isoWhiskerLeft _ τ.symm ≪≫ (c s x).symm ≪≫ eqToIso (congrArg (fun f ↦ P f) h.symm) ≪≫
    c x e

lemma stalkComparison_hom_app (τ : P s ≅ 𝟭 (D S)) {V : C} (x : S ⟶ V) (e : V ⟶ V)
    (h : x ≫ e = s ≫ x) (M : D V) :
    (stalkComparison (c := c) τ x e h).hom.app M =
      τ.inv.app ((P x).obj M) ≫ (c s x).inv.app M ≫ eqToHom (by rw [h]) ≫ (c x e).hom.app M := by
  simp [stalkComparison, eqToHom_app]

/-- **Stalks of a pullback**: for `g : W ⟶ X` with `e_W ≫ g = g ≫ e_X`, an object `F` of `D X`
with `φ : P e_X F ≅ F` and a point `w : S ⟶ W` with `w ≫ e_W = s ≫ w`, the composition
isomorphism `P w (P g F) ≅ P (w ≫ g) F` intertwines the stalk structure of the pullback
`(P g F, pullbackComparison ≫ P g φ)` at `w` with the stalk structure of `(F, φ)` at `w ≫ g`. -/
theorem stalkComparison_pullbackComparison (hc : PullbackAssoc P c) (τ : P s ≅ 𝟭 (D S))
    {W X : C} (g : W ⟶ X) (eW : W ⟶ W) (eX : X ⟶ X) (hg : eW ≫ g = g ≫ eX) {F : D X}
    (φ : (P eX).obj F ≅ F) (w : S ⟶ W) (hw : w ≫ eW = s ≫ w)
    (hwg : (w ≫ g) ≫ eX = s ≫ (w ≫ g)) :
    (stalkComparison (c := c) τ w eW hw).hom.app ((P g).obj F) ≫
        (P w).map ((pullbackComparison (c := c) g eW eX hg).hom.app F ≫ (P g).map φ.hom) ≫
        (c w g).inv.app F =
      (c w g).inv.app F ≫ (stalkComparison (c := c) τ (w ≫ g) eX hwg).hom.app F ≫
        (P (w ≫ g)).map φ.hom := by
  have nat₁ := (c w g).inv.naturality φ.hom
  have nat₂ := τ.inv.naturality ((c w g).inv.app F)
  simp only [Functor.comp_map, Functor.id_map] at nat₁ nat₂
  simp only [stalkComparison_hom_app, pullbackComparison_hom_app, Functor.map_comp,
    Category.assoc]
  rw [nat₁, reassoc_of% nat₂]
  refine congrArg (τ.inv.app _ ≫ ·) ?_
  simp only [← Category.assoc]
  refine congrArg (· ≫ (P (w ≫ g)).map φ.hom) ?_
  simp only [Category.assoc]
  rw [← cancel_epi ((c (s ≫ w) g).hom.app F ≫ (c s w).hom.app ((P g).obj F))]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  have k₁ : (P s).map ((c w g).hom.app F) ≫ (P s).map ((c w g).inv.app F) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  have k₂ : (P w).map ((c eW g).hom.app F) ≫ (P w).map ((c eW g).inv.app F) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  rw [reassoc_of% (hc.hom_app s w g F), reassoc_of% k₁, Iso.hom_inv_id_app_assoc,
    pullbackComp_hom_app_comp_eqToHom_left_assoc (c := c) hw.symm,
    reassoc_of% (hc.hom_app w eW g F), reassoc_of% k₂, eqToHom_map, pullbackComp_hom_app_comp_eqToHom_right_assoc (c := c) w hg,
    hc.hom_app_comp_map_hom_app_assoc, Iso.hom_inv_id_app, Category.comp_id]
  simp only [eqToHom_trans_assoc]

/-- `stalkComparison_pullbackComparison`, for a structure isomorphism `ψ` of the pullback given
through its underlying morphism, bracketed as the condition on a morphism of algebras. -/
theorem stalkComparison_pullbackComparison' (hc : PullbackAssoc P c) (τ : P s ≅ 𝟭 (D S))
    {W X : C} (g : W ⟶ X) (eW : W ⟶ W) (eX : X ⟶ X) (hg : eW ≫ g = g ≫ eX) {F : D X}
    (φ : (P eX).obj F ≅ F) (ψ : (P eW).obj ((P g).obj F) ⟶ (P g).obj F)
    (hψ : ψ = (pullbackComparison (c := c) g eW eX hg).hom.app F ≫ (P g).map φ.hom)
    (w : S ⟶ W) (hw : w ≫ eW = s ≫ w) (hwg : (w ≫ g) ≫ eX = s ≫ (w ≫ g)) :
    (c w g).inv.app F ≫ ((stalkComparison (c := c) τ (w ≫ g) eX hwg).hom.app F ≫
        (P (w ≫ g)).map φ.hom) =
      ((stalkComparison (c := c) τ w eW hw).hom.app ((P g).obj F) ≫ (P w).map ψ) ≫
        (c w g).inv.app F := by
  rw [hψ, Category.assoc]
  exact (stalkComparison_pullbackComparison hc τ g eW eX hg φ w hw hwg).symm

end Stalk

/-! ### Algebras over the overcategory -/

section Over

variable {T : C}

/-- A family of pullbacks on `C` induces one on `Over T`, through the underlying morphisms. -/
lemma PullbackAssoc.over (hc : PullbackAssoc P c) :
    PullbackAssoc (C := Over T) (D := fun V ↦ D V.left)
      (fun {X Y : Over T} (f : X ⟶ Y) ↦ P f.left)
      (fun {X Y Z : Over T} (f : X ⟶ Y) (g : Y ⟶ Z) ↦ c f.left g.left) :=
  fun f g h ↦ hc f.left g.left h.left

variable (c) in
/-- The pullback of algebras `(F, φ : P e_X F ≅ F)` along `g : W ⟶ X` over `T` with
`e_W ≫ g = g ≫ e_X`: `P g F` with `P e_W (P g F) ≅ P g (P e_X F) ≅ P g F`. -/
noncomputable def IsoAlgebra.overPullback {X W : Over T} (eX : X ≅ X) (eW : W ≅ W) {g : W ⟶ X}
    (hg : eW.hom ≫ g = g ≫ eX.hom) :
    Endofunctor.IsoAlgebra (P eX.hom.left) ⥤ Endofunctor.IsoAlgebra (P eW.hom.left) :=
  Endofunctor.IsoAlgebra.mapOfNatIso
    (pullbackComparison (c := c) g.left eW.hom.left eX.hom.left
      (Over.left_comp_left_eq_of_comp_eq hg))

variable (c) in
/-- An algebra `(F, φ)` for `P e` as an algebra for `P e^{n+1}`, with the iterated structure
isomorphism. -/
noncomputable def IsoAlgebra.overPowSucc {X : Over T} (e : X ≅ X) (n : ℕ)
    (G : Endofunctor.IsoAlgebra (P e.hom.left)) :
    Endofunctor.IsoAlgebra (P (e.powSucc n).hom.left) :=
  Endofunctor.IsoAlgebra.mk G.carrier
    (e.powSuccStr (fun f ↦ P f.left) (fun f f' ↦ c f.left f'.left) G.str n)

variable (c) in
/-- The stalk of algebras at a point `x : S ⟶ V` with `x ≫ e = s ≫ x`, for `τ : P s ≅ 𝟭`. -/
noncomputable def IsoAlgebra.stalk {S : C} {s : S ⟶ S} (τ : P s ≅ 𝟭 (D S)) {V : C} (x : S ⟶ V) (e : V ⟶ V)
    (h : x ≫ e = s ≫ x) :
    Endofunctor.IsoAlgebra (P e) ⥤ Endofunctor.IsoAlgebra (𝟭 (D S)) :=
  Endofunctor.IsoAlgebra.mapOfNatIso (stalkComparison (c := c) τ x e h)

/-- **Stalks of iterated pullbacks of algebras**: the composition isomorphism
`P w (P g F) ≅ P (w ≫ g) F` is an isomorphism between the stalk at `w` of the `(n + 1)`-st
iterate of the pullback of `F` along `g`, and the stalk at `w ≫ g` of the `(n + 1)`-st iterate
of `F`. -/
theorem IsoAlgebra.nonempty_stalk_overPowSucc_overPullback_iso (hc : PullbackAssoc P c)
    {X W : Over T} (eX : X ≅ X) (eW : W ≅ W) {g : W ⟶ X} (hg : eW.hom ≫ g = g ≫ eX.hom)
    (F : Endofunctor.IsoAlgebra (P eX.hom.left)) (n : ℕ) {S : C} {s : S ⟶ S}
    (τ : P s ≅ 𝟭 (D S)) (w : S ⟶ W.left) (hw : w ≫ (eW.powSucc n).hom.left = s ≫ w)
    (hwg : (w ≫ g.left) ≫ (eX.powSucc n).hom.left = s ≫ (w ≫ g.left)) :
    Nonempty ((IsoAlgebra.stalk c τ w _ hw).obj
        (IsoAlgebra.overPowSucc c eW n ((IsoAlgebra.overPullback c eX eW hg).obj F)) ≅
      (IsoAlgebra.stalk c τ (w ≫ g.left) _ hwg).obj (IsoAlgebra.overPowSucc c eX n F)) := by
  have hgn := Iso.powSucc_hom_comp_eq_comp_powSucc_hom eW eX hg n
  refine ⟨Endofunctor.IsoAlgebra.isoMk ((c w g.left).app F.carrier).symm ?_⟩
  change (c w g.left).inv.app F.carrier ≫
      ((stalkComparison (c := c) τ (w ≫ g.left) _ hwg).hom.app F.carrier ≫
        (P (w ≫ g.left)).map
          (eX.powSuccStr (fun f ↦ P f.left) (fun f f' ↦ c f.left f'.left) F.str n).hom) =
    ((stalkComparison (c := c) τ w _ hw).hom.app ((P g.left).obj F.carrier) ≫
        (P w).map (eW.powSuccStr (fun f ↦ P f.left) (fun f f' ↦ c f.left f'.left)
          ((IsoAlgebra.overPullback c eX eW hg).obj F).str n).hom) ≫
      (c w g.left).inv.app F.carrier
  exact stalkComparison_pullbackComparison' hc τ g.left _ _
    (Over.left_comp_left_eq_of_comp_eq hgn) _ _
    (Iso.powSuccStr_hom_eq_of_hom_eq (P := fun {X Y : Over T} (f : X ⟶ Y) ↦ P f.left)
      (c := fun {X Y Z : Over T} (f : X ⟶ Y) (g : Y ⟶ Z) ↦ c f.left g.left) hc.over eW eX g hg
      F.str ((IsoAlgebra.overPullback c eX eW hg).obj F).str rfl n) w hw hwg

end Over

end CategoryTheory
