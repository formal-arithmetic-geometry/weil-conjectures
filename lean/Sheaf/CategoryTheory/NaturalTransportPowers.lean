/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Endomorphism
public import Sheaf.CategoryTheory.NaturalTransportInduction

/-! # Powers of an endomorphism induced by natural transport

Source: main-20261015 blueprint, sec-trace-formula/sk-thm-trace-transport,
prop-trf-karoubi-independence.proof.md, final sentence on Frobenius transport,
expanded by the DAG's abstract power identity
(blueprint: lem-trf-global-frobenius-iterate-formula).

The functor powers and repeated transport are the existing `NaturalTransport.power`
and `NaturalTransport.repeated`. The structure-map composite below is defined without
any invertibility assumption.
-/

@[expose] public section

set_option autoImplicit false

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.NaturalTransport

/-- The ordered composite `φ^[m] : G^m K ⟶ K` of an arbitrary endofunctor algebra.
The empty composite is the identity; the successor is `G(φ^[m]) ≫ φ`.
This expands to `G^(m-1)(φ) ≫ ... ≫ G(φ) ≫ φ` for positive `m`.

Source: main-20261015 blueprint, prop-trf-karoubi-independence.proof.md,
final Frobenius-transport sentence, expanded in the DAG statement and Step 1
(blueprint: lem-trf-global-frobenius-iterate-formula). -/
def structureComposite {A : Type u₁} [Category.{v₁} A] {G : A ⥤ A}
    (K : Endofunctor.Algebra G) : (m : ℕ) → ((power G m).obj K.a ⟶ K.a)
  | 0 => 𝟙 K.a
  | m + 1 => G.map (structureComposite K m) ≫ K.str

/-- Powers of `C(φ) ∘ t_K` are the repeated natural transport followed by `C(φ^[m])`.
Neither the natural transformation nor the algebra structure map is assumed invertible.

Source: main-20261015 blueprint, sec-trace-formula/sk-thm-trace-transport,
prop-trf-karoubi-independence.proof.md, final sentence on Frobenius transport;
abstract identity extracted and expanded by the DAG
(blueprint: lem-trf-global-frobenius-iterate-formula).

Proof plan:
1. Use the arbitrary-structure-map clause of def-weil-endofunctor-fixed-pair-category.
   Write `u_m = structureComposite K m` and `v_m = repeated C G t K.a m`.
   By the displayed composites, `u_1 = φ`, `v_1 = t_K`,
   `u_(m+1) = G(u_m) ≫ φ` and `v_(m+1) = v_m ≫ t_(G^m K)`.
2. The case `m = 1` is the definition of `F`. Naturality of `t` at
   `u_m : G^m K ⟶ K` gives `C(u_m) ≫ t_K = t_(G^m K) ≫ C(G(u_m))`.
3. Induct on positive `m`. Substitute the induction hypothesis in `F^(m+1) = F ∘ F^m`.
   The naturality equation changes `v_m ≫ C(u_m) ≫ t_K ≫ C(φ)` into
   `v_m ≫ t_(G^m K) ≫ C(G(u_m)) ≫ C(φ)`.
   Functoriality of `C` and the recursions identify this with
   `v_(m+1) ≫ C(u_(m+1))`. Only associativity and functoriality are used. -/
theorem inducedEndomorphism_pow
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (G : A ⥤ A) (C : A ⥤ B) (t : C ⟶ G ⋙ C) (K : Endofunctor.Algebra G)
    (m : ℕ) (hm : 1 ≤ m) :
    (End.of (t.app K.a ≫ C.map K.str)) ^ m =
      repeated C G t K.a m ≫ C.map (structureComposite K m) := by
  sorry

end CategoryTheory.NaturalTransport
