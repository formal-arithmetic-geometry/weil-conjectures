/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Double dualization preserves injections of finite modules over a Noetherian domain

Source: Stacks Project, Tag 0EB8 (`more-algebra-lemma-sequence-reflexive`), proof of the
injectivity of `j` (blueprint: lem-per-finite-injection-bidual-injective).
-/

@[expose] public section

universe u v w

namespace LinearMap

/-- Over a commutative Noetherian domain, the double dual of an injective map between finite
modules is injective. Here `Module.Dual R W` is `W →ₗ[R] R`, `f.dualMap φ = φ.comp f`,
and `f.dualMap.dualMap x φ = x (φ.comp f)`.

Source: Stacks Project, Tag 0EB8 (`more-algebra-lemma-sequence-reflexive`), proof of the
injectivity of `j` (blueprint: lem-per-finite-injection-bidual-injective).

Proof plan:
1. Put `S = R ∖ {0}` and let `K` be the fraction field. Localization preserves the injection
   `f` by `lem-weil-pbc-localization-module-exact`, and `K` is flat over `R` by
   `lem-weil-pbc-localization-flat`.
2. Identify localization with tensoring by `K`, using
   `lem-weil-pbc-localization-tensor-product`: apply it to `(K, K, id)` and `(P, P_K)`,
   where the denominators already act invertibly on `K ⊗[R] P`. The unit isomorphism then
   identifies `K ⊗[R] P` with `P_K`. By
   `lem-weil-pbc-flat-base-change-hom-finitely-presented`, including its Noetherian
   finite-module clause, obtain the dual comparison for `P = U, V`, sending `φ/s` to
   the functional `p/t ↦ φ(p)/(s*t)`. Direct evaluation verifies compatibility with `f`.
3. By `lem-trf-vector-subspace-complement`, split the image of the localized injection
   inside `V_K`. Extend a functional on `U_K` by zero on the complement. Restriction of
   functionals from `V_K` to `U_K` is therefore surjective.
4. For `φ : U*`, represent an extension by `ψ/s`. Equality of localized functionals gives
   a nonzero `t` with `t • (ψ.comp f - s • φ) = 0`, by the fraction equality in
   `lem-weil-pbc-localization-module-exact`. Thus `(t • ψ).comp f = (t*s) • φ`, with
   `t*s ≠ 0`; the cokernel of `f.dualMap` is torsion.
5. If `f.dualMap.dualMap x = 0`, evaluating at `t • ψ` gives `(t*s) * x φ = 0`.
   Domain cancellation implies `x φ = 0` for every `φ`, hence `x = 0`. Apply this to a
   difference of two elements with equal images to obtain injectivity.
-/
theorem dualMap_dualMap_injective_of_injective_of_finite
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {U : Type v} [AddCommGroup U] [Module R U] [Module.Finite R U]
    {V : Type w} [AddCommGroup V] [Module R V] [Module.Finite R V]
    (f : U →ₗ[R] V) (hf : Function.Injective f) :
    Function.Injective f.dualMap.dualMap := by
  sorry

end LinearMap
