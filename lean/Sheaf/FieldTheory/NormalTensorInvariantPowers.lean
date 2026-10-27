/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Lemmas

import WeilConjectures.FieldTheory.NormalExtensionFixedField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.FieldTheory.FiniteSeparableTensorFieldReduced
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Invariant powers in a reduced normal field tensor product

Source: Stacks Project, More on Algebra, Tag 09EU, proof of `lemma-galois-relative`,
with Fields, Tag 030M, for normal extensions that need not be separable.
(blueprint: lem-sfb-normal-tensor-invariant-powers).
-/

@[expose] public section

universe u v w

set_option autoImplicit false

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- An invariant of the reduced tensor product with a finite normal extension has a
positive power in the scalar field. In characteristic zero the exponent is one;
in characteristic `p > 0` it can be a power of `p`.

The fixedness hypothesis is written on representatives: for every automorphism `σ`
and every lift `t` of `x`, the image of `(id ⊗ σ)(t)` is again `x`. This is exactly
fixedness for the induced action on the quotient, since ring homomorphisms preserve
nilpotents. It specifies the canonical action without choosing a lift of `x`.

Source: Stacks Project, More on Algebra, Tag 09EU, proof of `lemma-galois-relative`,
corrected for inseparable normal extensions using Fields, Tag 030M.
(blueprint: lem-sfb-normal-tensor-invariant-powers).

Proof:
1. Put `G = Aut_K(E)` and `S = E^G`. The extension is algebraic by finite dimension.
   By lem-weil-pbc-normal-extension-purely-inseparable-then-galois (Fields 030M),
   `S/K` is purely inseparable and `E/S` is separable and normal. A finite spanning
   set over `K` also spans over `S`. Each `K`-automorphism fixes `S`, and each
   `S`-automorphism fixes `K`, so `G = Aut_S(E)` is finite by
   lem-weil-pbc-finite-galois-fixed-field. In characteristic zero `S = K` by
   def-weil-pbc-finite-purely-inseparable-extension.
2. The canonical tensor maps from lem-weil-pbc-algebra-tensor-pushout-universal-property
   preserve nilpotents. Lift `x` to `t`. In characteristic zero the tensor is reduced
   by lem-weil-pbc-finite-separable-tensor-field-reduced, interchanging the factors;
   hence `t` is fixed, and set `y = t`, `q = 1`. In characteristic `p`, each
   `σ(t) - t` is nilpotent. Finiteness of `G` gives a common `p^a` at least their
   nilpotence exponents. Frobenius (def-weil-ring-frobenius) gives
   `σ(t^(p^a)) - t^(p^a) = (σ(t) - t)^(p^a) = 0`. Set `y = t^(p^a)`, `q = p^a`.
   Thus `y` is fixed and its quotient image is `x^q`.
3. Choose a `K`-basis of `L` by lem-weil-pbc-vector-space-basis-through-vector.
   Scalar extension (def-weil-vector-space-scalar-extension) makes its tensors
   with one an `E`-basis. Write `y` as a finite sum `∑ bᵢ ⊗ eᵢ`. Uniqueness of
   coordinates and fixedness imply that every `eᵢ` belongs to `S`. This uses no
   finiteness of `L/K`.
4. In characteristic zero, `S = K`, so balancing gives `y = l ⊗ 1`, hence the
   quotient image `x = overline(l ⊗ 1)`. In characteristic `p`, choose a common
   `p^b` making every `eᵢ^(p^b)` belong to `K`, using
   def-weil-pbc-finite-purely-inseparable-extension. Frobenius and the tensor
   multiplication give `y^(p^b) = l ⊗ 1` with
   `l = ∑ bᵢ^(p^b) eᵢ^(p^b)` in `L`. In the quotient this is
   `x^(p^(a+b)) = overline(l ⊗ 1)`, with positive exponent. For an empty sum use
   `l = 0`, `b = 0`. The characteristic cases also give the general positive-power
   assertion. -/
theorem exists_pow_eq_scalar_of_normal_invariant
    (K : Type u) (L : Type v) (E : Type w)
    [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
    [FiniteDimensional K E] [Normal K E]
    (x : (L ⊗[K] E) ⧸ nilradical (L ⊗[K] E))
    (hx : ∀ (σ : E ≃ₐ[K] E) (t : L ⊗[K] E),
      Ideal.Quotient.mk (nilradical (L ⊗[K] E)) t = x →
        Ideal.Quotient.mk (nilradical (L ⊗[K] E))
          (Algebra.TensorProduct.map (AlgHom.id K L) σ.toAlgHom t) = x) :
    (∃ (N : ℕ), 1 ≤ N ∧ ∃ (l : L),
      x ^ N = Ideal.Quotient.mk (nilradical (L ⊗[K] E)) (l ⊗ₜ[K] (1 : E))) ∧
    (CharZero K → ∃ (l : L),
      x = Ideal.Quotient.mk (nilradical (L ⊗[K] E)) (l ⊗ₜ[K] (1 : E))) ∧
    (∀ (p : ℕ), 0 < p → CharP K p → ∃ (r : ℕ) (l : L),
      x ^ (p ^ r) = Ideal.Quotient.mk (nilradical (L ⊗[K] E))
        (l ⊗ₜ[K] (1 : E))) := by
  sorry

end Algebra.TensorProduct
