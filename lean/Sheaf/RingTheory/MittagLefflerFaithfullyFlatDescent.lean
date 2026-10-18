/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Sheaf.RingTheory.IsMittagLeffler
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Faithfully flat descent of Mittag-Leffler modules

Source: Stacks Project, Algebra, Tag 05A5, lemma-ffdescent-ML
(blueprint: lem-trf-mittag-leffler-faithfully-flat-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v w i t

open scoped TensorProduct

namespace Module

/-- Mittag-Leffler modules descend along faithfully flat ring maps.

Source: Stacks Project, Algebra, Tag 05A5, lemma-ffdescent-ML.
The index universe and the test-module universe are shared across scalar extension;
both are arbitrary upper bounds on the ring and module universes. No equality
between the universes of `R`, `S`, and `M` is imposed.

1. By `lem-trf-module-finitely-presented-directed-colimit` (Tag 058G), write `M`
   as a nonempty directed colimit of finitely presented modules `M_i`, with maps
   `f_i : M_i → M` and transition maps `f_ij : M_i → M_j`.
2. Scalar extension preserves this colimit and finite presentations. Apply
   `lem-trf-mittag-leffler-eventual-domination` (Tag 059E) to `S ⊗[R] M`:
   for every `i`, choose `j ≥ i` such that the scalar extension of `f_ij`
   dominates the scalar extension of `f_i`.
3. Form the pushout `N` of `f_i` and `f_ij`, with leg `g : M_j → N`.
   Tensoring with `S` preserves the pushout, since scalar extension is a left adjoint.
4. By `lem-trf-domination-pushout-universal-injective` (Tag 0AUM), the domination
   from Step 2 makes the scalar extension of `g` universally injective over `S`.
5. Apply `lem-trf-faithfully-flat-universal-injective-reflection` to deduce that
   `g` is universally injective over `R`.
6. Apply the pushout criterion again: `f_ij` dominates `f_i`. For every `i` such
   a `j` exists, so the converse eventual-domination criterion proves that `M`
   is Mittag-Leffler. No flatness assumption on `M` is used.
(blueprint: lem-trf-mittag-leffler-faithfully-flat-descent)
-/
theorem isMittagLeffler_of_faithfullyFlat
    (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [AddCommGroup M]
    [Algebra R S] [Module R M] [Module.FaithfullyFlat R S]
    (hM : Module.IsMittagLeffler.{v, max v w, max u v w i, max u v w t}
      S (S ⊗[R] M)) :
    Module.IsMittagLeffler.{u, w, max u v w i, max u v w t} R M := by
  sorry

end Module
