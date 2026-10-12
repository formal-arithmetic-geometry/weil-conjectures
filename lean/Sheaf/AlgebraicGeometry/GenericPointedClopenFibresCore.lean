/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! Core geometric spreading statement for pointed clopen fibres.

Source: Stacks Project, Tag 055N, using Tags 04KV and 055G.
(blueprint: new-lem-sbc-generic-pointed-clopen-fibres-core)
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- The geometric shrinking step produces an open neighbourhood of `y` on which the
preconnectedness conclusion holds; containment in a prescribed open is handled separately.

Source: Stacks Project, Tag 055N, passage from a pointed clopen generic fibre to connected
fibres, using Tags 04KV and 055G.
Proof: pass to the reduced closure of `y`, form the open and closed subscheme represented by
`A`, and apply generic connectedness of fibres to its geometrically connected generic fibre.
Transport the resulting open back to `T`; fibre homeomorphisms identify its fibres with
`g ⁻¹' {t} ∩ A`.

(blueprint: new-lem-sbc-generic-pointed-clopen-fibres-core) -/
theorem exists_open_preconnected_fibres_of_pointed_clopen_core {P T : Scheme.{u}}
    (g : P ⟶ T) [LocallyOfFiniteType g] [QuasiCompact g]
    (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) (y : T) (V : Set T) (A : Set P)
    (hV : IsOpen V) (hyV : y ∈ V)
    (hA : IsClopen {q : g ⁻¹' (V ∩ closure {y}) | (q : P) ∈ A})
    (hconn : IsPreconnected (g ⁻¹' {y} ∩ A)) (hpoint : σ y ∈ A) :
    ∃ U : Set T, IsOpen U ∧ y ∈ U ∧
      ∀ t ∈ U ∩ closure {y}, IsPreconnected (g ⁻¹' {t} ∩ A) := by sorry

end AlgebraicGeometry
