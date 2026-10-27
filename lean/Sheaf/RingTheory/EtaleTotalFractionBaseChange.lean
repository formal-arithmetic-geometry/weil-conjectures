/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q08
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Etale.Field

/-! # Total fraction rings and étale base change

Source: Stacks Project, Tag 0EN6, proof of `lemma-meromorphic-quasi-coherent`,
the displayed total-fraction comparison, specialized to a reduced Noetherian base.
(blueprint: lem-sfb-etale-total-fraction-base-change)
-/

@[expose] public section

universe u

open scoped TensorProduct

/-- Total fraction rings commute with étale base change over a reduced Noetherian ring.
The equivalence is an equivalence of `B`-algebras for the action through the right tensor
factor, and the fraction-tensor formula specifies the canonical comparison uniquely.

Source: Stacks Project, Tag 0EN6, proof of `lemma-meromorphic-quasi-coherent`,
reduced Noetherian specialization.
(blueprint: lem-sfb-etale-total-fraction-base-change)

Proof:
1. Étaleness and `lem-weil-pbc-flat-morphism-affine-criterion` give flatness of `B`
   over `A` (`def-weil-pbc-flat-ring-map`). Tensor the injective multiplication map
   by each non-zero-divisor with `B`; its injectivity proves preservation of
   non-zero-divisors, also when `B` is zero.
2. By `lem-weil-pbc-localization-base-change`, after interchanging tensor factors,
   `C = Q(A) ⊗[A] B` is the localization of `B` at the images of non-zero-divisors
   of `A`. Every element is `j(b)/j(f(s))`. The localization zero criterion and
   Step 1 imply injectivity of `j : B → C`.
3. Apply `lem-weil-pbc-reduced-noetherian-total-ring-fractions` to express `Q(A)`
   as the finite product of the fields at its minimal primes. Apply
   `lem-weil-pbc-tensor-finite-product` to obtain `C` as the product of their base
   changes. The module comparison preserves multiplication and one on pure tensors,
   hence is a ring and `B`-algebra comparison.
4. Use `lem-weil-pbc-fibre-product-affine-spectra` and
   `lem-weil-pbc-etale-scheme-base-change` on each factor. By
   `lem-weil-pbc-etale-algebra-over-field-product`, each factor is a finite product
   of finite separable field extensions. Thus `C` is a finite product of fields,
   including the empty product.
5. If `t` is a non-zero-divisor in `B`, multiplication by `j(t)` is injective in `C`:
   the localization zero criterion reduces this to regularity of `t` and of the
   images of denominators. In a product of fields injective multiplication means
   every coordinate is nonzero, so `j(t)` is a unit. The empty product also has this
   property, since the sole element of the zero ring is a unit.
6. The localization universal property gives `C → Q(B)` from Step 1 and
   `Q(B) → C` from Step 5. Their fraction formulas are respectively `b/f(s)` and
   `j(b)/j(t)`. The localization equivalence relation makes both well-defined and
   they preserve the `B`-algebra structure. Their composites fix every fraction,
   so they are inverse. The identity `(a/s) ⊗ b = j(f(a)b)/j(f(s))` gives the stated
   formula. A unital map from zero forces `B = 0`; maps to zero and this case
   require no nontriviality assumption.
-/
theorem etale_total_fraction_base_change
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsReduced A]
    [AlgebraicGeometry.Etale
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B)))] :
    ∃ h : ∀ s : nonZeroDivisors A, algebraMap A B s ∈ nonZeroDivisors B,
      ∃ e : @AlgEquiv B (FractionRing A ⊗[A] B) (FractionRing B) _ _ _
          (Algebra.TensorProduct.rightAlgebra (R := A) (A := FractionRing A) (B := B)) _,
        ∀ (a : A) (s : nonZeroDivisors A) (b : B),
          e (IsLocalization.mk' (FractionRing A) a s ⊗ₜ[A] b) =
            IsLocalization.mk' (FractionRing B) (algebraMap A B a * b)
              ⟨algebraMap A B s, h s⟩ := by
  sorry
