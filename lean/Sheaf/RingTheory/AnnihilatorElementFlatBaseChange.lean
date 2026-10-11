/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Maps

/-! # Annihilator of an element under flat base change

Source: Stacks Project, Algebra, Lemma Tag 07T8 (`lemma-annihilator-flat-base-change`),
first assertion with `M = R` and `m = x`
(blueprint: lem-weil-pbc-annihilator-element-flat-base-change).
-/

@[expose] public section

universe u v

namespace RingHom

/--
Source: Stacks Project, Algebra, Lemma Tag 07T8, first assertion
(blueprint: lem-weil-pbc-annihilator-element-flat-base-change).

Let `φ : R →+* S` be flat and `x : R`. The annihilator ideal of the image of
`x` is the extension of the annihilator ideal of `x`. The proof tensors the
exact sequence given by multiplication by `x` with the flat `R`-module `S`.

1. Put `I = Ann_R(x)`. Multiplication by `x` has kernel `I`, so the sequence
   `0 → I → R → R`, with inclusion followed by multiplication by `x`, is exact.
2. Flatness (`def-weil-pbc-flat-ring-map`) preserves this exact sequence after
   tensoring with `S` (`lem-weil-pbc-flat-tensor-exact`). Identify `R ⊗[R] S`
   with `S` by `r ⊗ s ↦ φ(r)s`. Multiplication by `x` then becomes multiplication
   by `φ(x)`, and the inclusion becomes `α : I ⊗[R] S → S`,
   `a ⊗ s ↦ φ(a)s`. Thus the image of `α` is the annihilator of `φ(x)`.
3. The image of `α` consists of finite sums of `φ(a)s` with `a ∈ I` and `s ∈ S`.
   This is exactly `Ideal.map φ I`, giving the asserted equality.
-/
theorem annihilator_element_flat_base_change {R : Type u} {S : Type v}
    [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.Flat) (x : R) :
    Module.annihilator S (Ideal.span ({φ x} : Set S)) =
      Ideal.map φ (Module.annihilator R (Ideal.span ({x} : Set R))) := by
  sorry

end RingHom
