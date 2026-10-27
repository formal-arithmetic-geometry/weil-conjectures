/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # First Koszul homology base change for a flat quotient

Source: Stacks Project, More on Algebra, Tag 063Q, lemma-base-change-H1-regular.
(blueprint: lem-sfb-koszul-h1-flat-quotient-base-change-surjective).

The comparison is specified on all cycles. Its tensor-algebra linearity is written on
pure scalar tensors and pure module tensors; additivity extends this identity to all
scalars and elements. This avoids choosing a second module instance on the tensor product.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory
open scoped TensorProduct

namespace ExteriorAlgebra

/-- If the quotient by a finite sequence is flat over the parameter ring, the canonical
comparison on first Koszul homology is surjective. The first identity is precisely
`B ⊗[A] A'`-linearity for its natural tensor action. The last clause gives the image of
`[z] ⊗ a'`: the coefficients of its representative are `bᵢ ⊗ a'` when those of `z` are `bᵢ`.
It also characterizes the comparison uniquely, since every homology class has a cycle
representative and pure tensors generate the source. No flatness of either algebra is assumed.

Source: Stacks Project, More on Algebra, Tag 063Q, lemma-base-change-H1-regular.
(blueprint: lem-sfb-koszul-h1-flat-quotient-base-change-surjective).

Proof:
1. Put `I = (f)`, `E = B^r`, `Z = ker d₁`, and `H = Z / im d₂`. The Koszul differential
   gives exact sequences `0 → I → B → B/I → 0`, `Z → E → I → 0`, and
   `⋀² E → Z → H → 0` (def-weil-pbc-koszul-complex).
2. Exterior bases identify the base changes in degrees zero, one and two with the
   Koszul terms over `B ⊗[A] A'`. The maps send `(b e_J) ⊗ a'` to `(b ⊗ a') e_J`.
   The formulas for both differentials show that these identifications commute with them
   (def-weil-pbc-module-tensor-product and def-weil-pbc-koszul-complex).
3. Flatness of `B/I` makes `I ⊗ A' → B ⊗ A'` injective by
   lem-weil-pbc-flat-quotient-tensor-injective, conjugating by tensor flips if needed.
   Right exactness for `Z → E → I → 0` then makes `Z ⊗ A' → ker d'₁` surjective
   (lem-weil-pbc-tensor-right-exact).
4. Right exactness for `⋀² E → Z → H → 0` identifies `H ⊗ A'` with the quotient of
   `Z ⊗ A'` by the tensorized boundaries. The map to the new homology kills those
   boundaries by step 2, and therefore descends. Step 3 makes the descended map onto.
5. The construction sends `[z] ⊗ a'` to the class with coefficients `bᵢ ⊗ a'`.
   Multiplication by `b ⊗ c'` sends this to the class with coefficients `b bᵢ ⊗ c'a'`,
   proving the displayed linearity identity. Pure tensors generate, giving full linearity.
   Empty sequences and zero rings require no change to this argument. -/
theorem exists_koszulH1_baseChange_surjective
    (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
    (r : ℕ) (f : Fin r → B)
    [Module.Flat A (B ⧸ Ideal.span (Set.range f))] :
    ∃ β : (((ModuleCat.restrictScalars (algebraMap A B)).obj
        ((koszulComplex B r f).homology 1)) ⊗[A] A') →+
        (koszulComplex (B ⊗[A] A') r (fun i ↦ f i ⊗ₜ[A] (1 : A'))).homology 1,
      Function.Surjective β ∧
      (∀ (b : B) (c : A') (h : (koszulComplex B r f).homology 1) (a : A'),
        β ((b • h) ⊗ₜ[A] (c * a)) = (b ⊗ₜ[A] c) • β (h ⊗ₜ[A] a)) ∧
      (∀ (z : (koszulComplex B r f).cycles 1) (a : A'),
        ∃ z' : (koszulComplex (B ⊗[A] A') r
            (fun i ↦ f i ⊗ₜ[A] (1 : A'))).cycles 1,
          (∀ i : Fin r,
            (exteriorPower.oneEquiv (B ⊗[A] A') (Fin r →₀ (B ⊗[A] A'))
              ((koszulComplex (B ⊗[A] A') r
                (fun j ↦ f j ⊗ₜ[A] (1 : A'))).iCycles 1 z')) i =
              (exteriorPower.oneEquiv B (Fin r →₀ B)
                ((koszulComplex B r f).iCycles 1 z)) i ⊗ₜ[A] a) ∧
          β (((koszulComplex B r f).homologyπ 1 z) ⊗ₜ[A] a) =
            (koszulComplex (B ⊗[A] A') r
              (fun i ↦ f i ⊗ₜ[A] (1 : A'))).homologyπ 1 z') := by
  sorry

end ExteriorAlgebra
