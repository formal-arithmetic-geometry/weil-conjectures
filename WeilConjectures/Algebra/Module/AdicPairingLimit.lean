/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.RingTheory.Filtration
public import WeilConjectures.AlgebraicGeometry.ProEtale.IntegralAdicCohomology

/-!
# `p`-adic pairings from compatible-free families of finite-level pairings

Let `A`, `B` be free `ℤ_p`-modules of finite rank with endomorphisms `F_A`, `F_B` and `c ∈ ℤ_p`.
Suppose that for every `m` there is a pairing `P : A × B ⟶ ℤ_p` which is a `c`-similitude
modulo `pᵐ`, `P(F_A x, F_B y) ≡ c P(x, y)`, and whose kernels modulo `pᵐ` are controlled by a
fixed power `pᵉ` (if `P(x, -) ≡ 0` then `pᵉ x ∈ pᵐ A`, and symmetrically). The pairings at the
different levels need not be compatible. Then there is a pairing `P : A × B ⟶ ℤ_p` which is an
exact `c`-similitude with trivial left and right kernels
(`LinearMap.exists_isSimilitude_of_forall_level`).

The proof is by compactness: in the compact space of matrices over `ℤ_p`, the pairings satisfying
the conditions at level `m` form a decreasing sequence of nonempty closed sets.

This is how the finite-level Poincaré dualities with coefficients `ℤ/ℓᵐ`, which need not be
compatible with each other, give an `ℓ`-adic Poincaré duality, hence one over `ℚ̄_ℓ`.
-/

@[expose] public section

open Topology

namespace LinearMap

variable {p : ℕ} [Fact p.Prime] {A B ι κ : Type*} [AddCommGroup A] [Module ℤ_[p] A]
  [AddCommGroup B] [Module ℤ_[p] B] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

end LinearMap
