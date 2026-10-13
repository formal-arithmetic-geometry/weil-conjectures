/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # Fibrewise dense constant dimension opens

Source: Stacks Project, Tag 054T.
(blueprint: lem-sbc-flat-fibre-dimension-strata-core)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- Fibrewise dense constant dimension opens.

Source: Stacks Project, Tags 054T and 054U.
Proof: Restrict f to the inverse image of U. By Tag 045U, its Cohen-Macaulay locus is open and
fibrewise dense. Restrict further to that locus and use Tag 02NM to decompose it into open and
closed pieces of relative dimension n, indexed by natural numbers. Their union is the
Cohen-Macaulay locus, so is fibrewise dense. Their images in X are open because both restriction
inclusions are open immersions. For t in U, pullback associativity identifies the restricted fibre
with f.fiber t. Each piece has equidimensional fibres of dimension n by Tag 02NJ; hence its local
topological dimension is n. Local dimension is unchanged by inclusion of an open fibre subscheme,
giving the displayed equality in the original fibre. Fibres outside U do not meet these opens, so
the dimension conclusion there is vacuous. Empty fibres satisfy density of the empty union. This
constructs the opens without choosing arbitrary data from an unproved existence theorem.
(blueprint: lem-sbc-flat-fibre-dimension-strata-core) -/
theorem exists_fibre_dimension_opens_of_flat_restrict
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)] :
    ∃ V : ℕ → X.Opens,
      (∀ t : T, t ∈ U → Dense {z : f.fiber t | ∃ n : ℕ, f.fiberι t z ∈ V n}) ∧
      (∀ (n : ℕ) (x : X), x ∈ V n →
        topologicalKrullDimAt (f.asFiber x) = (n : WithBot ℕ∞)) := by sorry

end AlgebraicGeometry
