/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.CategoryTheory.NaturalTransportInduction
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

/-! # Powers of an endomorphism induced by natural transport

Source: main-20261015 blueprint, sec-trace-formula/sk-thm-trace-transport,
prop-trf-karoubi-independence.proof.md, final sentence on Frobenius transport,
expanded by the DAG's abstract power identity
(blueprint: lem-trf-global-frobenius-iterate-formula). The current blueprint's
sec-trace-formula/sk-lem-tf-frobenius-convention,
lem-trf-frobenius-operator-compact-description.md describes the global iterate.

The functor powers and repeated transport are those of `NaturalTransportInduction`.
The structure map is arbitrary: neither it nor the transport is assumed invertible.
-/

@[expose] public section

set_option autoImplicit false

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.NaturalTransport

/-- The ordered composite `φ ∘ G(φ) ∘ ... ∘ G^(m-1)(φ) : G^m K ⟶ K`.
At zero it is the identity; the successor is `G(φ^[m]) ≫ φ`.
Source: main-20261015 blueprint, sec-trace-formula/sk-thm-trace-transport,
prop-trf-karoubi-independence.proof.md, final Frobenius-transport sentence, expanded in
the DAG statement and Step 1 (blueprint: lem-trf-global-frobenius-iterate-formula). -/
def structureComposite {A : Type u₁} [Category.{v₁} A] {G : A ⥤ A}
    (K : Endofunctor.Algebra G) : (m : ℕ) → ((power G m).obj K.a ⟶ K.a)
  | 0 => 𝟙 K.a
  | m + 1 => G.map (structureComposite K m) ≫ K.str

/-- Powers of the endomorphism induced by a natural transport on an arbitrary algebra.
Source: main-20261015 blueprint, sec-trace-formula/sk-thm-trace-transport,
prop-trf-karoubi-independence.proof.md, final sentence on Frobenius transport; abstract
identity extracted and expanded by the DAG
(blueprint: lem-trf-global-frobenius-iterate-formula); the current blueprint describes
this iterate in sec-trace-formula/sk-lem-tf-frobenius-convention,
lem-trf-frobenius-operator-compact-description.md.

Proof plan:
1. Use the arbitrary-structure-map clause of def-weil-endofunctor-fixed-pair-category.
   Write `u_m = structureComposite K m` and `v_m = repeated C G t K.a m`.
   The displayed composites give `u_1 = K.str`, `v_1 = t.app K.a`, and the recurrences
   `u_(m+1) = G.map u_m ≫ K.str` and `v_(m+1) = v_m ≫ t.app (G^m K)`.
2. At `m = 1`, the formula is the definition of the induced endomorphism `F`.
   Naturality of `t` at `u_m : G^m K ⟶ K` says
   `C.map u_m ≫ t.app K.a = t.app (G^m K) ≫ C.map (G.map u_m)`.
3. For the successor, write `F^(m+1) = F ∘ F^m`, substitute the induction hypothesis,
   and apply the naturality equality from step 2. Functoriality of `C` and associativity
   combine the structure factors into `C.map u_(m+1)` and the transport factors into
   `v_(m+1)`. Induction on positive integers gives the result. No inverse or cancellation
   is used, so noninvertible structure maps and transports are included. -/
theorem inducedEndomorphism_pow
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (G : A ⥤ A) (C : A ⥤ B) (t : C ⟶ G ⋙ C) (K : Endofunctor.Algebra G)
    (m : ℕ) (hm : 1 ≤ m) :
    (End.of (t.app K.a ≫ C.map K.str)) ^ m =
      repeated C G t K.a m ≫ C.map (structureComposite K m) := by
  have h : ∀ n : ℕ, (End.of (t.app K.a ≫ C.map K.str)) ^ n =
      repeated C G t K.a n ≫ C.map (structureComposite K n) := by
    intro n
    induction n with
    | zero =>
      change 𝟙 (C.obj K.a) = 𝟙 (C.obj K.a) ≫ C.map (𝟙 K.a)
      exact ((Category.id_comp _).trans (C.map_id K.a)).symm
    | succ n ih =>
      rw [pow_succ', End.mul_def, ih]
      simp only [repeated, structureComposite, C.map_comp, Category.assoc]
      rw [← Category.assoc (C.map (structureComposite K n)), t.naturality]
      simp only [Functor.comp_map, Category.assoc]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact h (1 + n)

end CategoryTheory.NaturalTransport
