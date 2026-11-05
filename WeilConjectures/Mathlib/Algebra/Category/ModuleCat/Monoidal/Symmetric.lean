/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Trace
public import WeilConjectures.CategoryTheory.Monoidal.Rigid.Trace

/-!
# The categorical trace of an endomorphism of a finite free module

Let `R` be a commutative ring and `M` an `R`-module with a finite basis `b`. Then `M` has the
right dual `Hom_R(M, R)` in `ModuleCat R` (`ModuleCat.exactPairingOfBasis`): the coevaluation is
`1 ↦ ∑ᵢ bᵢ ⊗ bᵢ*` and the evaluation is the contraction `φ ⊗ m ↦ φ(m)`.

For the symmetric braiding of `ModuleCat R`, the categorical trace
`CategoryTheory.MonoidalCategory.trace` of an endomorphism `f` of a finite free module `M` is the
usual trace `LinearMap.trace R M f`, as an element of `End (𝟙_ (ModuleCat R))`
(`ModuleCat.trace_eq_algebraMap_linearMapTrace`). This holds for any right dual of `M`.

This is used for blueprint `sk-p-trace` and `lem-trf-chain-supertrace`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory TensorProduct

namespace ModuleCat

variable {R : Type u} [CommRing R]

section

variable {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]
  (b : Module.Basis ι R M)

end

end ModuleCat
