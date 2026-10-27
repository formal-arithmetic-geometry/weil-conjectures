/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q142
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Sheaf.FieldTheory.FieldTower
public import WeilConjectures.Mathlib.Algebra.CharP.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Bases and degrees in the Frobenius-image field tower

Source: Stacks Project, Fields, Tag 09G9, `lemma-multiplicativity-degrees`, and Varieties,
Tags 03SM and 0CCG, `definition-absolute-frobenius` and `remark-n-fold-relative-frobenius`.
The basis transport is the explicit algebraic refinement recorded in the DAG.
(blueprint: lem-sfb-frobenius-image-field-tower-degree)
-/

@[expose] public section

universe u

namespace FieldExtension

/-- The Frobenius-image tower has constant adjacent degree, with the powers of any given
basis as its adjacent bases. The total degree is the corresponding power of the first degree.
The family `L` is fixed by `hL` to the actual power-image subfields; `extendScalars h`
is the same subfield `L i`, equipped with its scalar structure over `L (i + 1)`.

Source: Stacks Project, Fields, Tag 09G9, `lemma-multiplicativity-degrees`; Varieties,
Tags 03SM and 0CCG, `definition-absolute-frobenius` and `remark-n-fold-relative-frobenius`.
(blueprint: lem-sfb-frobenius-image-field-tower-degree)

Proof:
1. The endomorphism `iterateFrobeniusOfPrime` of `def-weil-ring-frobenius` sends `x` to
   `x^(p^i)`. Its kernel is zero: a nonzero kernel element and its inverse would give
   `1 = 0`. Applying this to a difference proves injectivity. Its image is closed under
   field operations, so corestriction gives the displayed field isomorphism.
2. The identity `(x^p)^(p^i) = x^(p^(i+1))` shows that this isomorphism carries `L 1`
   onto `L (i+1)`, and also that `L (i+1)` is contained in `L i`. The zeroth image is `K`.
3. Expand any preimage in the given basis, as in `def-weil-pbc-free-module`, then apply
   the isomorphism. Its coefficients now belong to `L (i+1)`, proving spanning.
4. Lift the coefficients of a relation through the isomorphism on `L 1`. Injectivity
   and independence of the original basis force all coefficients to vanish. Thus the
   powers form a basis of size `d`; `def-weil-vector-space-dimension` and
   `def-pc-field-tower` identify the adjacent degree with `d`.
5. For `n=0`, the singleton basis `(1)` gives degree one. Inductively apply
   `lem-weil-pbc-field-degree-multiplicativity` to `L (n+1) ⊆ L n ⊆ K`:
   finiteness is preserved and the degrees multiply to `d^n * d = d^(n+1)`.
   No surjectivity of Frobenius on `K` is used. -/
theorem frobenius_image_field_tower_degree
    (K : Type u) [Field K] (p : ℕ) (hp : p.Prime) [CharP K p]
    (L : ℕ → Subfield K)
    (hL : ∀ i : ℕ, L i =
      (iterateFrobeniusOfPrime K hp (CharP.cast_eq_zero K p) i).fieldRange)
    (d : ℕ) (hd : degree (L 1) K = (d : WithTop ℕ))
    (b : Module.Basis (Fin d) (L 1) K) :
    L 0 = ⊤ ∧ degree (L 0) K = 1 ∧
    (∀ i : ℕ, ∃ α : K ≃+* L i,
      (∀ x : K, (α x : K) = x ^ (p ^ i)) ∧
      (fun x : K ↦ (α x : K)) '' (L 1 : Set K) = (L (i + 1) : Set K) ∧
      ∃ h : L (i + 1) ≤ L i,
        (∃ c : Module.Basis (Fin d) (L (i + 1)) (Subfield.extendScalars h),
          ∀ j : Fin d, (c j : K) = b j ^ (p ^ i)) ∧
        degree (L (i + 1)) (Subfield.extendScalars h) = (d : WithTop ℕ)) ∧
    ∀ n : ℕ, degree (L n) K = ((d ^ n : ℕ) : WithTop ℕ) := by
  sorry

end FieldExtension
