/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.Flat.Equalizer

/-! # Relative finite presentation across a square-zero base ideal

Source: Stacks Project, Tag 06AG, `lemma-deform-property`, proof of clause (13),
general remark (I), and clause (11).
(blueprint: lem-sfb-relative-flat-algebra-fp-lift)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace RingHom

/-- Finite presentation of a relative algebra lifts across a square-zero base ideal when
its target is flat over the base. There is no flatness assumption on the intermediate ring.
The ideal `(I.map f).map g` is `I.map (g.comp f)` by `Ideal.map_map`, so the quotient
map below is precisely the canonical map `A/IA → C/IC`.

Source: Stacks Project, Tag 06AG, `lemma-deform-property`, proof of clause (13),
using clause (11) and general remark (I).
(blueprint: lem-sfb-relative-flat-algebra-fp-lift)

Proof plan, following the six steps of the DAG node:
1. Reduce a finite polynomial presentation modulo the base ideal. Coefficient reduction
   gives the reduced presentation, proving the forward direction without flatness
   (`def-weil-pbc-finitely-presented-algebra`, `def-weil-pbc-mv-polynomial-ring`).
2. Lift finitely many generators of the reduced algebra to `C`. Their generated
   subalgebra `D` satisfies `C = D + IC`; substituting this identity again and using
   `I² = 0` gives `C = D`. Thus evaluation from `P = A[x₁,...,xₙ]` is surjective
   (the same two definition nodes).
3. For every base module `M`, identify `(R/I) ⊗ M` with `M/IM` by the mutually inverse
   formulas `r̄ ⊗ m ↦ rm mod IM` and `m mod IM ↦ 1̄ ⊗ m`. These maps are natural in
   `M`; coefficient reduction also identifies `P/IP` with `(A/IA)[x₁,...,xₙ]`
   (`def-weil-pbc-module-tensor-product`, `def-weil-pbc-mv-polynomial-ring`).
4. Put `K = ker(P → C)`. Since `C` is flat over `R`, tensoring its short exact
   presentation with `R/I` stays short exact by
   `lem-weil-pbc-flat-quotient-tensor-injective`. Hence `K/IK` identifies with the
   kernel of the reduced polynomial presentation, compatibly with polynomial scalars.
5. By `lem-weil-pbc-finite-presentation-surjection-kernel-fg`, that reduced kernel
   has finitely many generators. Lift them to `K` and let `L` be their generated
   ideal in `P`. Lifting their polynomial coefficients yields `K = L + IK`.
6. Substitute once more: `K = L + IL + I²K = L`. Thus `P → C` has finitely generated
   kernel and is a finite presentation (`def-weil-pbc-finitely-presented-algebra`).
   Empty lists, the zero ring, and ideals that are not finitely generated are allowed.
-/
theorem finitePresentation_iff_quotient_of_square_zero_of_flat
    {R : Type u} {A : Type v} {C : Type w} [CommRing R] [CommRing A] [CommRing C]
    (f : R →+* A) (g : A →+* C) (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hflat : (g.comp f).Flat) :
    g.FinitePresentation ↔
      (Ideal.quotientMap ((I.map f).map g) g Ideal.le_comap_map).FinitePresentation := by
  sorry

end RingHom
