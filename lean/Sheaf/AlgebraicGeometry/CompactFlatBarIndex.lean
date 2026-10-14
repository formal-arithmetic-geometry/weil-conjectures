/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.CompactFlatSourceBarTower
public import Sheaf.AlgebraicGeometry.CompactFlatTelescopeBlocks

/-! # The indexing preorder for the enlarged bar construction

Source: the least-block and target-chain paragraph of
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: def-sc-compact-flat-bar-index).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
namespace CompactFlatBarIndex

variable {Y : Scheme.{u}}
  {L : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
  {l : ∀ n : ℕ, L n ⟶ L (n + 1)}
  (D : CompactFlatFiniteSubcomplexDiagrams Y L l)
  (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
  (t : ∀ n : ℕ, E n ⟶ E (n + 1))
  (p : ∀ n : ℕ, L n ⟶ CochainComplex.mappingCone (flatTelescopeDifferential E t))

open FlatTelescopeBlocks

noncomputable def leastBlock (j : D.index) : ℕ :=
  by
    classical
    exact Nat.find (factor_diagram_object E t D j (D.augmentationTo p j))

lemma leastBlock_spec (j : D.index) :
    ∃ g : D.diagram.obj j ⟶ block E t (leastBlock D E t p j),
      g ≫ toTelescope E t (leastBlock D E t p j) = D.augmentationTo p j :=
  by
    classical
    exact Nat.find_spec (factor_diagram_object E t D j (D.augmentationTo p j))

lemma leastBlock_mono (hp : ∀ n : ℕ, l n ≫ p (n + 1) = p n) :
    Monotone (leastBlock D E t p) := by
  classical
  intro j k h
  obtain ⟨g, hg⟩ := leastBlock_spec D E t p k
  apply Nat.find_min'
  refine ⟨D.diagram.map (homOfLE h) ≫ g, ?_⟩
  rw [Category.assoc, hg]
  exact D.augmentationTo_naturality p hp (homOfLE h)

noncomputable def factorTo (j : D.index) (k : ℕ) (h : leastBlock D E t p j ≤ k) :
    D.diagram.obj j ⟶ block E t k :=
  (leastBlock_spec D E t p j).choose ≫ transitionLE E t h

lemma factorTo_toTelescope (j : D.index) (k : ℕ) (h : leastBlock D E t p j ≤ k) :
    factorTo D E t p j k h ≫ toTelescope E t k = D.augmentationTo p j := by
  rw [factorTo, Category.assoc, transitionLE_toTelescope]
  exact (leastBlock_spec D E t p j).choose_spec

/-- Sources retain their original order, targets form the natural-number chain,
and a source points to precisely the blocks through which it factors. -/
def Rel : D.index ⊕ ℕ → D.index ⊕ ℕ → Prop
  | .inl j, .inl k => j ≤ k
  | .inl j, .inr k => leastBlock D E t p j ≤ k
  | .inr _, .inl _ => False
  | .inr j, .inr k => j ≤ k

/-- The order is proved from the least-block monotonicity. -/
@[instance_reducible]
def preorder (hp : ∀ n : ℕ, l n ≫ p (n + 1) = p n) : Preorder (D.index ⊕ ℕ) where
  le := Rel D E t p
  lt a b := Rel D E t p a b ∧ ¬ Rel D E t p b a
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl j := by cases j <;> exact le_rfl
  le_trans j k m hj hk := by
    cases j <;> cases k <;> cases m
    · exact le_trans hj hk
    · exact le_trans ((leastBlock_mono D E t p hp) hj) hk
    · exact False.elim hk
    · exact le_trans hj hk
    · exact False.elim hj
    · exact False.elim hj
    · exact False.elim hk
    · exact le_trans hj hk

/-- A separate type records the parameters determining the enlarged order. -/
def Index (_hp : ∀ n : ℕ, l n ≫ p (n + 1) = p n) : Type u := D.index ⊕ ℕ

instance (hp : ∀ n : ℕ, l n ≫ p (n + 1) = p n) :
    Preorder (Index D E t p hp) := preorder D E t p hp

variable (hp : ∀ n : ℕ, l n ≫ p (n + 1) = p n)

noncomputable def obj : Index D E t p hp →
    CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ
  | .inl j => D.diagram.obj j
  | .inr k => block E t k

noncomputable def augmentation : ∀ j : Index D E t p hp,
    obj D E t p hp j ⟶ CochainComplex.mappingCone (flatTelescopeDifferential E t)
  | .inl j => D.augmentationTo p j
  | .inr k => toTelescope E t k

noncomputable def map {j k : Index D E t p hp} (h : j ⟶ k) :
    obj D E t p hp j ⟶ obj D E t p hp k := by
  have hh : Rel D E t p j k := leOfHom h
  cases j <;> cases k
  · exact D.diagram.map (homOfLE hh)
  · exact factorTo D E t p _ _ hh
  · exact False.elim hh
  · exact transitionLE E t hh

lemma map_augmentation {j k : Index D E t p hp} (h : j ⟶ k) :
    map D E t p hp h ≫ augmentation D E t p hp k = augmentation D E t p hp j := by
  cases j <;> cases k
  · exact D.augmentationTo_naturality p hp _
  · exact factorTo_toTelescope D E t p _ _ _
  · exact False.elim (leOfHom h)
  · exact transitionLE_toTelescope E t _

lemma map_id (j : Index D E t p hp) : map D E t p hp (𝟙 j) = 𝟙 _ := by
  cases j with
  | inl j => simp [map, obj]
  | inr k =>
    let := HomologicalComplex.mono_of_mono_f (toTelescope E t k) (fun i ↦ inferInstance)
    apply (cancel_mono (toTelescope E t k)).1
    simpa only [augmentation, Category.id_comp] using
      map_augmentation D E t p hp (j := .inr k) (k := .inr k) (𝟙 _)

lemma map_comp {j k m : Index D E t p hp} (h : j ⟶ k) (g : k ⟶ m) :
    map D E t p hp (h ≫ g) = map D E t p hp h ≫ map D E t p hp g := by
  cases m with
  | inr m =>
    let := HomologicalComplex.mono_of_mono_f (toTelescope E t m) (fun i ↦ inferInstance)
    apply (cancel_mono (toTelescope E t m)).1
    change map D E t p hp (h ≫ g) ≫ augmentation D E t p hp (.inr m) =
      (map D E t p hp h ≫ map D E t p hp g) ≫ augmentation D E t p hp (.inr m)
    rw [map_augmentation, Category.assoc, map_augmentation, map_augmentation]
  | inl m =>
    cases k with
    | inr k => exact False.elim (leOfHom g)
    | inl k =>
      cases j with
      | inr j => exact False.elim (leOfHom h)
      | inl j =>
        dsimp only [map, obj]
        rw [← D.diagram.map_comp]
        congr 1

/-- The enlarged diagram has specified, strictly compatible maps into the telescope. -/
noncomputable def diagram : Index D E t p hp ⥤
    CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ where
  obj := obj D E t p hp
  map := map D E t p hp
  map_id := map_id D E t p hp
  map_comp := map_comp D E t p hp

noncomputable def cocone : Cocone (diagram D E t p hp) where
  pt := CochainComplex.mappingCone (flatTelescopeDifferential E t)
  ι.app := augmentation D E t p hp
  ι.naturality _ _ h := by
    simpa [diagram] using map_augmentation D E t p hp h

/-- Inclusion of the source indexing preorder. -/
def sourceOrder : D.index →o Index D E t p hp where
  toFun := Sum.inl
  monotone' := by intro j k h; exact h

/-- Inclusion of the target chain. -/
def targetOrder : ℕ →o Index D E t p hp where
  toFun := Sum.inr
  monotone' := by intro j k h; exact h

/-- The least-block map is left adjoint to the target-chain inclusion. -/
noncomputable def retractOrder : Index D E t p hp →o ℕ where
  toFun j := match j with
    | .inl j => leastBlock D E t p j
    | .inr k => k
  monotone' := by
    intro j k h
    cases j <;> cases k
    · exact leastBlock_mono D E t p hp h
    · exact h
    · exact False.elim h
    · exact h

lemma retractOrder_le_iff (j : Index D E t p hp) (k : ℕ) :
    retractOrder D E t p hp j ≤ k ↔ j ≤ targetOrder D E t p hp k := by
  cases j <;> rfl

end CompactFlatBarIndex
end AlgebraicGeometry
