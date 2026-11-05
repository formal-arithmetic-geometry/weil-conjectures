/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Pole-order valuations on a function field

Let `E` be a finite separable extension of `k⟮y⟯` with `y` transcendental over `k`. The integral
closure of `k[y]` in `E` is a Dedekind domain with fraction field `E`; its height-one primes
give a family of valuations on `E` which are trivial on `k`, have finitely many poles at each
element, and such that the elements without poles are integral over `k[y]`, so that the
coefficients of their minimal polynomials over `k⟮y⟯` are polynomials in `y`.
-/

@[expose] public section

universe v

open Polynomial IntermediateField
open scoped WithZero

namespace FrobeniusClosedBasis

variable (k : Type*) {E : Type v} [Field k] [Field E] [Algebra k E]

end FrobeniusClosedBasis
