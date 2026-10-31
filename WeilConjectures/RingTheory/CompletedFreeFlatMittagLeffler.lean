/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.RingTheory.IsMittagLeffler
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import WeilConjectures.SecTraceFormula.ProductNoetherianFlatMittagLeffler
import WeilConjectures.TraceFormula.PureSubmoduleMittagLeffler
import WeilConjectures.TraceFormula.UniversallyExactFlatSubmodule
import WeilConjectures.RingTheory.CompletedFreeIntoProductUniversallyInjective

/-!
# Completed free modules are flat Mittag-Leffler

Source: Stacks Project, `flat.tex`, Tag 05DJ, lemma-completed-direct-sum-ML
(blueprint: lem-trf-completed-free-flat-mittag-leffler).
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

namespace Module

/-- The completion of the free module on an arbitrary set over a Noetherian
`I`-adically complete commutative ring is flat and Mittag-Leffler.
Here `A →₀ R` is the module of finitely supported families. Its completion is the
module of compatible classes modulo `I ^ n • ⊤`, with componentwise operations.
The degree-zero quotient is zero, so indexing the completion by all natural numbers
is equivalent to indexing by the positive integers.

Source: Stacks Project, `flat.tex`, Tag 05DJ, lemma-completed-direct-sum-ML
(blueprint: lem-trf-completed-free-flat-mittag-leffler).

Proof:
1. By `lem-trf-completed-free-into-product-universally-injective`, the canonical
   coordinate map from the completion of `A →₀ R` to `A → R` stays injective
   after tensoring with any module. Take its cokernel. Tensor right exactness
   (`lem-weil-pbc-tensor-right-exact`) gives a universally exact short exact
   sequence from the completion through `A → R` to that cokernel.
2. By `lem-trf-product-noetherian-flat-mittag-leffler`, the product `A → R` is
   flat. Apply `lem-trf-universally-exact-flat-submodule` to the sequence in
   step 1 to obtain flatness of the completion.
3. The same product theorem makes `A → R` Mittag-Leffler. Apply
   `lem-trf-pure-submodule-mittag-leffler` to the universally exact sequence
   from step 1 to obtain the Mittag-Leffler property of the completion.
-/
theorem completed_free_flat_mittag_leffler
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] (A : Type v) :
    Module.Flat R (AdicCompletion I (A →₀ R)) ∧
      Module.IsMittagLeffler.{u, max u v, w, t} R (AdicCompletion I (A →₀ R)) := by
  sorry

end Module
