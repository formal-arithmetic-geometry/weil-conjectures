/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.WeilObject.Sheaf.Stalk

/-!

# The iterated Frobenius operators of a Weil sheaf

Let `e : X ≅ X` be an automorphism. The trace formula for the `(n + 1)`-st Frobenius, `n : ℕ`,
uses the power `e^{n+1}` of `e` (`CategoryTheory.Iso.powSucc e n`) and, for a Weil sheaf
`(F, φ_F)` of `ℚ̄_ℓ`-modules for `e`, the `(n + 1)`-fold iterate of its structure isomorphism,
which makes `F` a Weil sheaf for `e^{n+1}` (`ProEtale.CondensedRing.WeilSheaf.powSucc`):
```
φ_F^{(n+2)} : (e^{n+1} ≫ e)^* F ≅ (e^{n+1})^* e^* F --(e^{n+1})^* φ_F--> (e^{n+1})^* F
  --φ_F^{(n+1)}--> F,
```
the first isomorphism being the composition isomorphism `ProEtale.CondensedRing.upperStarComp` of
pullbacks on module objects. The powers are indexed so that `n = 0` gives `e¹ = e`: the identity
isomorphism `𝟙^* ≅ 𝟭` of the pullback on module objects, which a power `e⁰ = 𝟙` would need, is
not available, and the trace formula does not use it.

The stalk at a geometric point `x̄` with `x̄ ≫ e^{n+1} = σ^{n+1} ≫ x̄` of the Weil sheaf
`(F, φ_F^{(n+1)})` for `e^{n+1}` (`ProEtale.CondensedRing.WeilSheaf.stalkFunctor`) is the stalk
of `F` with its `(n + 1)`-st Frobenius operator. For `x̄` the geometric point over an
`𝔽_{q^{n+1}}`-rational point this is the action of the Frobenius of `𝔽_{q^{n+1}}` on the stalk; no
fixed-point isomorphism for the first iterate is imposed.

## Main definitions

- `CategoryTheory.Iso.powSucc`: the power `e^{n+1}` of an automorphism.
- `CategoryTheory.Iso.powSuccStr`: the iterated structure isomorphism `(P e^{n+1}) a ≅ a` for a
  family of endofunctors `P` contravariant in endomorphisms up to composition isomorphisms.
- `ProEtale.CondensedRing.WeilSheaf.powSucc`: a Weil sheaf for `e` as a Weil sheaf for `e^{n+1}`,
  functorially in `ProEtale.CondensedRing.WeilSheaf.powSuccFunctor`.

## Implementation notes

The recursion is carried out in the generic `CategoryTheory.Iso.powSuccStr` and only then
instantiated with the pullbacks on module objects: done directly on module objects, the kernel
times out while checking the recursive definition.

The coherence of `φ_F^{(n+1)}` with the iterated structure isomorphism
`CategoryTheory.Endofunctor.IsoAlgebra.strIterate`, through the iterated composition isomorphism
`(e^{n+1})^* ≅ (e^*)^{n+1}`, and the identity relating `φ_F^{(n+m+2)}` to `φ_F^{(n+1)}` and
`φ_F^{(m+1)}` up to the composition isomorphisms, are not proved here.

-/

@[expose] public section

universe v u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Obj

namespace CategoryTheory.Iso

variable {C : Type u} [Category.{v} C] {X : C} (e : X ≅ X)

/-- The power `e.powSucc n = e^{n+1}` of an automorphism, defined recursively by `e¹ = e` and
`e^{n+2} = e^{n+1} ≫ e`. -/
def powSucc (e : X ≅ X) : ℕ → (X ≅ X)
  | 0 => e
  | n + 1 => powSucc e n ≪≫ e

@[simp]
lemma powSucc_zero : e.powSucc 0 = e :=
  rfl

lemma powSucc_succ (n : ℕ) : e.powSucc (n + 1) = e.powSucc n ≪≫ e :=
  rfl

@[simp]
lemma powSucc_refl (n : ℕ) : (Iso.refl X).powSucc n = Iso.refl X := by
  induction n with
  | zero => rfl
  | succ n ih => rw [powSucc_succ, ih, Iso.refl_trans]

/-- A morphism `s` with `e ≫ s = s` satisfies `e^{n+1} ≫ s = s`. -/
lemma powSucc_hom_comp_of_hom_comp {Y : C} {s : X ⟶ Y} (h : e.hom ≫ s = s) (n : ℕ) :
    (e.powSucc n).hom ≫ s = s := by
  induction n with
  | zero => exact h
  | succ n ih => rw [powSucc_succ, Iso.trans_hom, Category.assoc, h, ih]

/-- The iterated structure isomorphism `(P e^{n+1}) a ≅ a` of an object `a` with an isomorphism
`φ : P e a ≅ a`, for a family of endofunctors `P g` indexed by the endomorphisms `g` of `X`,
contravariant up to the composition isomorphisms `P (f ≫ g) ≅ P g ⋙ P f`: it is `φ` for `n = 0`,
and the composite `P (e^{n+1} ≫ e) a ≅ P e^{n+1} (P e a) ≅ P e^{n+1} a ≅ a` of the composition
isomorphism, `P e^{n+1} φ` and the iterated structure isomorphism for `n`. -/
noncomputable def powSuccStr {D : Type*} [Category D] (P : (X ⟶ X) → D ⥤ D)
    (comp : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f) {a : D} (φ : (P e.hom).obj a ≅ a) :
    ∀ n : ℕ, (P (e.powSucc n).hom).obj a ≅ a
  | 0 => φ
  | n + 1 =>
    (comp (e.powSucc n).hom e.hom).app a ≪≫ (P (e.powSucc n).hom).mapIso φ ≪≫
      powSuccStr P comp φ n

/-- The iterated structure isomorphisms are natural: a morphism `u : a ⟶ b` compatible with
`φ : P e a ≅ a` and `ψ : P e b ≅ b` is compatible with their iterates. -/
lemma powSuccStr_hom_naturality {D : Type*} [Category D] (P : (X ⟶ X) → D ⥤ D)
    (comp : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f) {a b : D} {φ : (P e.hom).obj a ≅ a}
    {ψ : (P e.hom).obj b ≅ b} (u : a ⟶ b) (hu : (P e.hom).map u ≫ ψ.hom = φ.hom ≫ u) (n : ℕ) :
    (P (e.powSucc n).hom).map u ≫ (e.powSuccStr P comp ψ n).hom =
      (e.powSuccStr P comp φ n).hom ≫ u := by
  induction n with
  | zero => exact hu
  | succ n ih =>
    change (P ((e.powSucc n).hom ≫ e.hom)).map u ≫ (comp _ _).hom.app b ≫
        (P (e.powSucc n).hom).map ψ.hom ≫ (e.powSuccStr P comp ψ n).hom =
      ((comp _ _).hom.app a ≫ (P (e.powSucc n).hom).map φ.hom ≫
        (e.powSuccStr P comp φ n).hom) ≫ u
    rw [(comp _ _).hom.naturality_assoc, Functor.comp_map, ← Functor.map_comp_assoc, hu,
      Functor.map_comp_assoc, ih, Category.assoc, Category.assoc]

end CategoryTheory.Iso

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] {F : C ⥤ C}

/-- A morphism `IsoAlgebra.mk a Φ ⟶ IsoAlgebra.mk b Ψ`, given by a morphism `u : a ⟶ b` commuting
with the structure isomorphisms. -/
def mkHom {a b : C} {Φ : F.obj a ≅ a} {Ψ : F.obj b ≅ b} (u : a ⟶ b)
    (h : F.map u ≫ Ψ.hom = Φ.hom ≫ u) : mk a Φ ⟶ mk b Ψ :=
  ObjectProperty.homMk { f := u, h := h }

@[simp]
lemma mkHom_hom_f {a b : C} {Φ : F.obj a ≅ a} {Ψ : F.obj b ≅ b} (u : a ⟶ b)
    (h : F.map u ≫ Ψ.hom = Φ.hom ≫ u) : (mkHom u h).hom.f = u :=
  rfl

lemma mkHom_id {a : C} {Φ : F.obj a ≅ a} (h : F.map (𝟙 a) ≫ Φ.hom = Φ.hom ≫ 𝟙 a) :
    mkHom (𝟙 a) h = 𝟙 (mk a Φ) :=
  rfl

lemma mkHom_comp {a b c : C} {Φ : F.obj a ≅ a} {Ψ : F.obj b ≅ b} {Θ : F.obj c ≅ c} (u : a ⟶ b)
    (v : b ⟶ c) (hu : F.map u ≫ Ψ.hom = Φ.hom ≫ u) (hv : F.map v ≫ Θ.hom = Ψ.hom ≫ v)
    (huv : F.map (u ≫ v) ≫ Θ.hom = Φ.hom ≫ u ≫ v) :
    mkHom (u ≫ v) huv = mkHom u hu ≫ mkHom v hv :=
  rfl

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] {X : Over (Spec (.of k))} {e : X ≅ X}

/-- A Weil sheaf `(F, φ_F)` for `e` as a Weil sheaf for `e^{n+1}`, with the iterated structure
isomorphism `φ_F^{(n+1)} : (e^{n+1})^* F ≅ F`: `φ_F^{(1)} = φ_F` and `φ_F^{(n+2)}` is the
composite `(e^{n+1} ≫ e)^* F ≅ (e^{n+1})^* e^* F ≅ (e^{n+1})^* F ≅ F` of the composition
isomorphism `upperStarComp`, `(e^{n+1})^* φ_F` and `φ_F^{(n+1)}`. -/
noncomputable def WeilSheaf.powSucc (F : WeilSheaf ℓ e) (n : ℕ) : WeilSheaf ℓ (e.powSucc n) :=
  IsoAlgebra.mk F.carrier
    (e.powSuccStr (fun g ↦ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
      (fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left) F.str n)

variable (e) in
/-- A Weil sheaf for `e` as a Weil sheaf for `e^{n+1}` (`WeilSheaf.powSucc`), as a functor: a
morphism of Weil sheaves for `e` is compatible with the iterated structure isomorphisms. -/
noncomputable def WeilSheaf.powSuccFunctor (n : ℕ) : WeilSheaf ℓ e ⥤ WeilSheaf ℓ (e.powSucc n) where
  obj F := WeilSheaf.powSucc ℓ F n
  map {F G} φ := IsoAlgebra.mkHom φ.hom.f
    (e.powSuccStr_hom_naturality (fun g ↦ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
      (fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left) (φ := F.str)
      (ψ := G.str) φ.hom.f φ.hom.h n)
  map_id _ := IsoAlgebra.mkHom_id _
  map_comp _ _ := IsoAlgebra.mkHom_comp _ _ _ _ _

@[simp]
lemma WeilSheaf.powSuccFunctor_obj (n : ℕ) (F : WeilSheaf ℓ e) :
    (WeilSheaf.powSuccFunctor ℓ e n).obj F = WeilSheaf.powSucc ℓ F n :=
  rfl

@[simp]
lemma WeilSheaf.powSuccFunctor_obj_carrier (n : ℕ) (F : WeilSheaf ℓ e) :
    ((WeilSheaf.powSuccFunctor ℓ e n).obj F).carrier = F.carrier := by
  rw [powSuccFunctor_obj, WeilSheaf.powSucc, IsoAlgebra.mk_carrier]

end AlgebraicGeometry.ProEtale.CondensedRing
