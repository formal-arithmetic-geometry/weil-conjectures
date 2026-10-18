/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Ideal.Operations

import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Finite prime intersections for principal radicals in a normalization

Source: Swanson–Huneke, *Integral Closure of Ideals, Rings, and Modules*, proof of
Proposition 4.8.2, printed p. 84; Definition 4.10.1, Proposition 4.10.3 and
Theorem 4.10.5 (Mori–Nagata), printed pp. 89–91
(blueprint: lem-trf-normalization-principal-minimal-primes).
-/

@[expose] public section

universe u v w

set_option autoImplicit false

namespace Ideal

/-- (blueprint: lem-trf-normalization-principal-minimal-primes)
For a Noetherian domain `R`, a fraction field `K`, and a finite field extension `F / K`,
the radical of a nonzero principal ideal in `integralClosure R F` is an intersection
of finitely many prime ideals. The family is allowed to be empty, with intersection `⊤`.

Source: Swanson–Huneke, proof of Proposition 4.8.2, p. 84, and Definition 4.10.1,
Proposition 4.10.3 and Theorem 4.10.5, pp. 89–91.

Proof:
1. Choose a finite `K`-basis of `F`. For each basis element `α`, take a monic relation
   of degree `n ≥ 1` with coefficients `cⱼ` in `K` and choose nonzero `d` in `R` clearing
   their denominators. Then `β = dα` satisfies the monic relation with coefficients
   `d^(n-j)cⱼ` in `R`, since `j < n`. Thus the scaled basis elements are integral.
2. Let `S` be the `R`-subalgebra they generate. It is finite over `R` by
   [lem-weil-pbc-finite-of-integral-generators], and integral by
   [lem-weil-pbc-finite-algebra-is-integral]. It is a Noetherian ring by
   [lem-weil-pbc-finite-type-algebra-noetherian], and a domain as a subring of `F`.
   Its fraction field contains `K` and every `α = β/d`, hence their entire `K`-span `F`.
3. The integral closure of `S` in `F` equals that of `R`: one inclusion extends a monic
   equation from `R` to `S`. For the reverse, `S[x]` is finite over `S` by
   [lem-weil-pbc-finite-of-integral-generators], so integral by
   [lem-weil-pbc-finite-algebra-is-integral]; [lem-weil-pbc-integral-transitive] then
   makes `x` integral over `R`.
4. Apply [lem-trf-normalization-integral-closure-krull] to `S` in its own fraction field
   `F`. By step 3 this makes `integralClosure R F` a Krull domain.
5. For nonzero `b`, [lem-trf-krull-principal-primary-decomposition] gives finitely many
   height-one primes `Pᵢ` containing `b` and ideals `Jᵢ = D ∩ bD_(Pᵢ)` with
   `bD = ⋂ᵢ Jᵢ` and `√Jᵢ = Pᵢ`.
6. A positive power in `bD` lies in every `Jᵢ`, giving one radical inclusion. Conversely,
   membership in every `Pᵢ` supplies positive exponents with `x^nᵢ ∈ Jᵢ`; their maximum
   supplies one power in every `Jᵢ`, hence in `bD`. If the family is empty, step 5 says
   `bD = D` and both sides are `⊤`. Taking `Qᵢ = Pᵢ` proves the assertion.
-/
theorem integralClosure_principal_radical_eq_finite_iInf_primes
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (F : Type w) [Field F] [Algebra K F] [FiniteDimensional K F]
    [Algebra R F] [IsScalarTower R K F]
    (b : integralClosure R F) (_hb : b ≠ 0) :
    ∃ (t : ℕ) (Q : Fin t → Ideal (integralClosure R F)),
      (∀ i : Fin t, (Q i).IsPrime) ∧
        (Ideal.span ({b} : Set (integralClosure R F))).radical = ⨅ i : Fin t, Q i := by
  sorry

end Ideal
