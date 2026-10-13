/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # Constant relative dimension opens for a flat finitely presented morphism

Source: Stacks Project, Tags 054T and 054U.
(blueprint: lem-sbc-flat-fibre-dimension-strata)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A flat locally finitely presented map over an open admits constant-dimension
opens covering every generic point of every fibre component over that open.

Source: Stacks Project, Tag 054T (Lemma 37.22.9), and the first sentence of
Tag 054U's proof.
Proof: apply Tag 054T to the restricted morphism over U. Its opens of relative
dimension n have fibrewise dense union. Fibres are locally of finite type over
fields, hence locally noetherian. In a locally noetherian space every component
generic point belongs to every dense open: near that point remove the other
finitely many components, and use density and specialization. Identify the
restricted fibres with the original fibres by pullback pasting. These
isomorphisms preserve generic points and local dimension. The source of the
restricted morphism is an open subscheme of X, so its dimension opens are also
opens of X. Local dimension is unchanged by the open immersion of each
restricted fibre into its original fibre. This gives both clauses below.
Empty fibres contribute no generic points; n is always a natural number
because the fibres are locally of finite type over a field.
(blueprint: lem-sbc-flat-fibre-dimension-strata) -/
theorem exists_fibre_dimension_strata_of_flat_restrict
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)] :
    ∃ V : ℕ → X.Opens,
      (∀ x : X, f x ∈ U →
        f.asFiber x ∈ genericPoints (f.fiber (f x)) → ∃ n : ℕ, x ∈ V n) ∧
      (∀ (n : ℕ) (x : X), x ∈ V n →
        topologicalKrullDimAt (f.asFiber x) = (n : WithBot ℕ∞)) := by sorry

end AlgebraicGeometry
