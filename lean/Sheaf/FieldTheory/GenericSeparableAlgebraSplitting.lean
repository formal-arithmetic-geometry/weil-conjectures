/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Splitting the reduction of a finite algebra after a separable extension

Source: blueprint, `sec-smooth-purity/sk-prop-sf-cbc`, proof of
`lem-weil-pbc-finite-pushforward-generic-constructible`; Stacks Project, More on Morphisms,
proof of Tag 02LM (blueprint: lem-weil-pbc-generic-separable-algebra-splitting).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace Algebra

/-- The reduction of a finite-dimensional commutative algebra over a field becomes a finite
product of finite purely inseparable fields after a finite separable extension.
Source: blueprint, proof of `lem-weil-pbc-finite-pushforward-generic-constructible`, generic
finite-algebra calculation; Stacks Project, proof of Tag 02LM.
(blueprint: lem-weil-pbc-generic-separable-algebra-splitting)

Proof:
1. By `lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum`, applied over the field K,
   C has finitely many prime ideals, all maximal, with intersection its nilradical N.
   The Chinese remainder theorem (`lem-pc-crt-ideal-quotient-product`) identifies C/N with
   the product of the finite residue fields E_i. For C = 0 the product is empty.
   N is nilpotent. Its image after tensoring with K' is nilpotent too; right exactness of
   tensor product identifies the quotient by that image with (C/N) tensor K'. Thus reducing
   C tensor K' gives the product of the reductions of E_i tensor K'.
2. Apply `lem-weil-pbc-separable-split-purely-inseparable-residue-fields` to the finite family
   E_i/K. It supplies a finite separable extension K'/K such that every prime of
   K' tensor E_i has a residue field finite purely inseparable over K'. Swap tensor factors
   to use the right-factor K'-algebra structure in the statement.
3. Apply `lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum` over K' to each tensor
   factor. Its finitely many primes are maximal and intersect in the nilradical. Apply
   `lem-pc-crt-ideal-quotient-product` to identify its reduction with their residue fields.
   By step 2 each of those fields is finite purely inseparable over K'.
4. Assemble these finite products over i to obtain the asserted K'-algebra isomorphism.
   The extension K'/K retains the finiteness and separability supplied in step 2.
-/
theorem exists_separable_extension_reduction_tensorProduct_equiv_pi
    (K : Type u) [Field K] (C : Type v) [CommRing C] [Algebra K C]
    [FiniteDimensional K C] :
    ∃ (K' : Type (max u v)) (hK' : Field K') (aK' : Algebra K K'),
      letI := hK'
      letI := aK'
      FiniteDimensional K K' ∧ Algebra.IsSeparable K K' ∧
        ∃ (n : ℕ) (L : Fin n → Type (max u v))
          (hL : ∀ j, Field (L j)) (aL : ∀ j, Algebra K' (L j)),
          letI := hL
          letI := aL
          letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := C) (B := K')
          (∀ j, FiniteDimensional K' (L j) ∧ IsPurelyInseparable K' (L j)) ∧
            Nonempty (((C ⊗[K] K') ⧸ nilradical (C ⊗[K] K')) ≃ₐ[K'] (∀ j, L j)) := by
  sorry

end Algebra
