/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin

/-! # Purely transcendental field extensions

Source: Stacks Project, Fields, Tag 030E, definition-transcendence (3).
(blueprint: def-trf-purely-transcendental-extension).
-/

@[expose] public section
set_option autoImplicit false

universe u v

namespace Algebra

/-- A field extension is purely transcendental if some algebraically independent subset
of the larger field generates it as a field. By `AlgebraicIndependent.aevalEquivField`,
this is precisely being isomorphic over the smaller field to a rational function field.
The empty set permits the trivial extension; no finiteness is imposed.
Source: Stacks Project, Fields, Tag 030E, definition-transcendence (3).
(blueprint: def-trf-purely-transcendental-extension). -/
def IsPurelyTranscendentalExtension (k : Type u) (K : Type v)
    [Field k] [Field K] [Algebra k K] : Prop :=
  ∃ t : Set K, AlgebraicIndependent k (fun x : t ↦ (x : K)) ∧
    IntermediateField.adjoin k t = ⊤

end Algebra
