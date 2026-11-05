/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisCompositum

/-!

# `Gal(F_K^sep / F_K·F^sep)` is a pro-`p` group, modulo tame ramification

Let `F = k'((t))`, `F_K = K((t))`, `Ω_K = F_K^alg` and `L' = F_K·F^sep ⊆ Ω_K`
(`AlgebraicGeometry.traitGenericSepCompositum`). The core of SGA 4½, [Th. finitude], Lemme 3.3,
is that `Gal(F_K^sep / L')` is a pro-`p` group (`p` the characteristic). This file reduces this
statement to the classical description of tame extensions of complete discretely valued fields
with algebraically closed residue field.

* **The Kummer extensions `F_K(t^{1/n})` lie in `L'`**
  (`AlgebraicGeometry.mem_traitGenericSepCompositum_of_pow_eq`): for `n` prime to `p`, every
  `n`-th root of `t` in `Ω_K` is the image of a root of the separable polynomial `Xⁿ - t` over `F`.
* **Units of `K⟦t⟧` are `n`-th powers** for `p ∤ n` (`PowerSeries.exists_pow_eq_of_isUnit`),
  the Hensel input of the Kummer description of tame extensions of `K((t))`.
* **A Cauchy argument** (`IsGalois.exists_finrank_eq_prime_pow`): a finite Galois extension
  `M / L` in which every element of prime-to-`p` degree over an intermediate field `E` lies in
  `E` has `p`-power degree.
* **Descent to finite subextensions**
  (`IntermediateField.exists_finiteDimensional_natDegree_minpoly_eq`): the degree of a separable
  element `α` over a field `E ⊆ Ω` is its degree over the subfield `F(coefficients) ⊆ E`, which is
  finite over `F` when `Ω / F` is algebraic.
* **The reduction** (`IntermediateField.exists_finrank_eq_prime_pow_of_forall_mem_sup` and
  `AlgebraicGeometry.exists_finrank_traitGenericSepCompositum_eq_pow`): if for every finite
  extension `E₀` of `F_K` in `Ω_K`, every separable element of prime-to-`p` degree over `E₀` lies in
  some `E₀(t^{1/n})` with `p ∤ n` (the tame closure of `E₀` is `E₀·F_K^tame`), then every finite
  Galois extension of `L'` has `p`-power degree, i.e. its Galois group is a `p`-group
  (`AlgebraicGeometry.isPGroup_traitGenericSepCompositum`).

-/

@[expose] public section

open Polynomial IntermediateField Module

universe u

namespace AlgebraicGeometry

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

end AlgebraicGeometry
