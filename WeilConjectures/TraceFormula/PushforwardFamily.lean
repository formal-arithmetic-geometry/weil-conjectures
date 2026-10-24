/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.PullbackFamily

/-!

# Iterated structure isomorphisms of a transport of algebras along a pushforward

Let `P` be a family of pullbacks on `C` with composition isomorphisms `c`, and let
`L : D X ⥤ D Y` be a functor between the categories over `X` and `Y`, together with
isomorphisms `bc a b : L ⋙ P b ≅ P a ⋙ L` for automorphisms `a`, `b` of `X`, `Y` over `T` with
`a ≫ f = f ≫ b`, satisfying the pasting law `hbc`. For instance `L` is the pushforward `f_*` and
`bc` the base-change morphisms of the Frobenius squares.

An algebra `(G, φ)` for `P e_X` is sent to the algebra `(L G, bc ≫ L φ)` for `P e_Y`
(`Endofunctor.IsoAlgebra.overPushforward`). This file proves that this transport commutes with the
iterated structure isomorphisms (`Endofunctor.IsoAlgebra.nonempty_overPowSucc_overPushforward_iso`),
and gives a form of this statement for functors given through equations
(`Endofunctor.IsoAlgebra.nonempty_overPowSucc_overPushforward_iso_of_eq`), as in
`WeilConjectures.TraceFormula.PullbackFamily`.

-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : C → Type*} [∀ X, Category (D X)]
  {P : ∀ {X Y : C}, (X ⟶ Y) → D Y ⥤ D X}
  (c : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
  {T : C} {X Y : Over T} {f : X ⟶ Y} (L : D X.left ⥤ D Y.left)
  (bc : ∀ (a : X ≅ X) (b : Y ≅ Y), a.hom ≫ f = f ≫ b.hom → (L ⋙ P b.hom.left ≅ P a.hom.left ⋙ L))

/-- The pasting law of the comparisons `bc` along the composition of automorphisms: the comparison
for `a ≫ a'` and `b ≫ b'` is the pasting of those for `a`, `b` and `a'`, `b'`, through the
composition isomorphisms `c`. -/
def PushforwardPaste : Prop :=
  ∀ (a a' : X ≅ X) (b b' : Y ≅ Y) (h : a.hom ≫ f = f ≫ b.hom) (h' : a'.hom ≫ f = f ≫ b'.hom)
    (h'' : (a ≪≫ a').hom ≫ f = f ≫ (b ≪≫ b').hom),
    Functor.whiskerLeft L (c b.hom.left b'.hom.left).hom ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (bc a' b' h').hom (P b.hom.left) ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (P a'.hom.left) (bc a b h).hom ≫ (Functor.associator _ _ _).inv =
      (bc (a ≪≫ a') (b ≪≫ b') h'').hom ≫ Functor.whiskerRight (c a.hom.left a'.hom.left).hom L

variable {c L bc}

/-- **The iterated structure isomorphisms of a transport along a pushforward**: the iterated
structure isomorphism of `(L G, bc ≫ L φ)` is `bc` for the iterated automorphisms, followed by `L`
of the iterated structure isomorphism of `(G, φ)`. -/
theorem Iso.powSuccStr_overPushforward (hbc : PushforwardPaste c L bc) (eX : X ≅ X) (eY : Y ≅ Y)
    (hf : eX.hom ≫ f = f ≫ eY.hom) {G : D X.left} (φ : (P eX.hom.left).obj G ≅ G) (n : ℕ) :
    (eY.powSuccStr (fun g ↦ P g.left) (fun g g' ↦ c g.left g'.left)
        ((bc eX eY hf).app G ≪≫ L.mapIso φ) n).hom =
      (bc (eX.powSucc n) (eY.powSucc n)
          (Iso.powSucc_hom_comp_eq_comp_powSucc_hom eX eY hf n)).hom.app G ≫
        L.map (eX.powSuccStr (fun g ↦ P g.left) (fun g g' ↦ c g.left g'.left) φ n).hom := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (c (eY.powSucc n).hom.left eY.hom.left).hom.app (L.obj G) ≫
        (P (eY.powSucc n).hom.left).map ((bc eX eY hf).hom.app G ≫ L.map φ.hom) ≫
        (eY.powSuccStr (fun g ↦ P g.left) (fun g g' ↦ c g.left g'.left)
          ((bc eX eY hf).app G ≪≫ L.mapIso φ) n).hom =
      (bc (eX.powSucc n ≪≫ eX) (eY.powSucc n ≪≫ eY)
          (Iso.powSucc_hom_comp_eq_comp_powSucc_hom eX eY hf (n + 1))).hom.app G ≫
        L.map ((c (eX.powSucc n).hom.left eX.hom.left).hom.app G ≫
          (P (eX.powSucc n).hom.left).map φ.hom ≫
          (eX.powSuccStr (fun g ↦ P g.left) (fun g g' ↦ c g.left g'.left) φ n).hom)
    have hn := (bc (eX.powSucc n) (eY.powSucc n)
      (Iso.powSucc_hom_comp_eq_comp_powSucc_hom eX eY hf n)).hom.naturality φ.hom
    simp only [Functor.comp_map] at hn
    have hp := NatTrans.congr_app (hbc (eX.powSucc n) eX (eY.powSucc n) eY
      (Iso.powSucc_hom_comp_eq_comp_powSucc_hom eX eY hf n) hf
      (Iso.powSucc_hom_comp_eq_comp_powSucc_hom eX eY hf (n + 1))) G
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id] at hp
    rw [ih, Functor.map_comp, Category.assoc, reassoc_of% hn, reassoc_of% hp, L.map_comp,
      L.map_comp]

variable (bc) in
/-- The transport of algebras for `P e_X` to algebras for `P e_Y` along `L`, through `bc`. -/
noncomputable def Endofunctor.IsoAlgebra.overPushforward (eX : X ≅ X) (eY : Y ≅ Y)
    (hf : eX.hom ≫ f = f ≫ eY.hom) :
    Endofunctor.IsoAlgebra (P eX.hom.left) ⥤ Endofunctor.IsoAlgebra (P eY.hom.left) :=
  Endofunctor.IsoAlgebra.mapOfNatIso (bc eX eY hf)

/-- **The transport along a pushforward commutes with the iterated structure isomorphisms.** -/
theorem Endofunctor.IsoAlgebra.nonempty_overPowSucc_overPushforward_iso
    (hbc : PushforwardPaste c L bc) (eX : X ≅ X) (eY : Y ≅ Y) (hf : eX.hom ≫ f = f ≫ eY.hom)
    (n : ℕ) (A : Endofunctor.IsoAlgebra (P eX.hom.left)) :
    Nonempty (Endofunctor.IsoAlgebra.overPowSucc c eY n
        ((Endofunctor.IsoAlgebra.overPushforward bc eX eY hf).obj A) ≅
      (Endofunctor.IsoAlgebra.overPushforward bc (eX.powSucc n) (eY.powSucc n)
        (Iso.powSucc_hom_comp_eq_comp_powSucc_hom eX eY hf n)).obj
        (Endofunctor.IsoAlgebra.overPowSucc c eX n A)) := by
  refine ⟨Endofunctor.IsoAlgebra.isoMk (Iso.refl _) ?_⟩
  simp only [Endofunctor.IsoAlgebra.overPushforward, Endofunctor.IsoAlgebra.overPowSucc,
    ← Endofunctor.IsoAlgebra.str_hom, Endofunctor.IsoAlgebra.mapOfNatIso_obj_str,
    Endofunctor.IsoAlgebra.mk_str, Endofunctor.IsoAlgebra.mk_carrier, Iso.refl_hom,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rw [Iso.powSuccStr_overPushforward hbc eX eY hf A.str n]
  rfl

/-- `Endofunctor.IsoAlgebra.nonempty_overPowSucc_overPushforward_iso` for categories and functors
given through equations, so that concrete instances can use their own categories and functors
without unfolding them (compare `Endofunctor.IsoAlgebra.nonempty_obj_obj_iso_of_eq`). -/
theorem Endofunctor.IsoAlgebra.nonempty_overPowSucc_overPushforward_iso_of_eq
    (hbc : PushforwardPaste c L bc) (eX : X ≅ X) (eY : Y ≅ Y) (hf : eX.hom ≫ f = f ≫ eY.hom)
    (n : ℕ) (𝒜X 𝒜Y 𝒜Xn 𝒜Yn : Type _) {i𝒜X : Category 𝒜X} {i𝒜Y : Category 𝒜Y}
    {i𝒜Xn : Category 𝒜Xn} {i𝒜Yn : Category 𝒜Yn} (A : 𝒜X) (Φ : 𝒜X ⥤ 𝒜Y) (Φn : 𝒜Xn ⥤ 𝒜Yn)
    (QX : 𝒜X ⥤ 𝒜Xn) (QY : 𝒜Y ⥤ 𝒜Yn)
    (h𝒜X : (⟨𝒜X, i𝒜X⟩ : Σ A : Type _, Category A) =
      ⟨Endofunctor.IsoAlgebra (P eX.hom.left), inferInstance⟩)
    (h𝒜Y : (⟨𝒜Y, i𝒜Y⟩ : Σ A : Type _, Category A) =
      ⟨Endofunctor.IsoAlgebra (P eY.hom.left), inferInstance⟩)
    (h𝒜Xn : (⟨𝒜Xn, i𝒜Xn⟩ : Σ A : Type _, Category A) =
      ⟨Endofunctor.IsoAlgebra (P (eX.powSucc n).hom.left), inferInstance⟩)
    (h𝒜Yn : (⟨𝒜Yn, i𝒜Yn⟩ : Σ A : Type _, Category A) =
      ⟨Endofunctor.IsoAlgebra (P (eY.powSucc n).hom.left), inferInstance⟩)
    (hΦ : HEq Φ (Endofunctor.IsoAlgebra.overPushforward bc eX eY hf))
    (hΦn : HEq Φn (Endofunctor.IsoAlgebra.overPushforward bc (eX.powSucc n) (eY.powSucc n)
      (Iso.powSucc_hom_comp_eq_comp_powSucc_hom eX eY hf n)))
    (hQX : HEq QX (Endofunctor.IsoAlgebra.overPowSuccFunctor c eX n))
    (hQY : HEq QY (Endofunctor.IsoAlgebra.overPowSuccFunctor c eY n)) :
    Nonempty (QY.obj (Φ.obj A) ≅ Φn.obj (QX.obj A)) := by
  cases h𝒜X
  cases h𝒜Y
  cases h𝒜Xn
  cases h𝒜Yn
  cases hΦ
  cases hΦn
  cases hQX
  cases hQY
  exact Endofunctor.IsoAlgebra.nonempty_overPowSucc_overPushforward_iso hbc eX eY hf n A

end CategoryTheory
