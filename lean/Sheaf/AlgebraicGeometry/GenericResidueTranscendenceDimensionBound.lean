module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Sheaf.AlgebraicGeometry.LocalDimensionFormulaGenericComponents
import WeilConjectures.AlgebraicGeometry.Dimension

/-!
# Dimension bound from generic residue-field transcendence degrees

Source: literature/stacks-project/morphisms.tex, Tag 0BAG,
lemma-alteration-dimension-general, using Tag 0BAE and Properties Tag 04MU
(blueprint: lem-sfb-generic-residue-transcendence-dimension-bound).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A locally finite type morphism to a locally Noetherian scheme has source dimension
bounded by the base dimension plus a bound for all generic residue transcendence degrees.
Source: literature/stacks-project/morphisms.tex, Tag 0BAG,
lemma-alteration-dimension-general
(blueprint: lem-sfb-generic-residue-transcendence-dimension-bound).

Proof:
1. If Y is empty, its topological Krull dimension is bottom, so the bound holds.
   Otherwise fix y in Y and set s = f(y).
2. Apply lem-sfb-local-dimension-formula-generic-components at y. It gives a
   finite nonempty set G of generic points of the components through y and
   dim O_{Y,y} + trdeg_{κ(s)} κ(y) ≤ dim O_{S,s} + E_y, where E_y is the
   maximum of the generic residue transcendence degrees on G. The hypothesis
   bounds each of these degrees by n, so E_y ≤ n. The degree at y is nonnegative.
   By lem-pc-scheme-dimension-local-rings for S, dim O_{S,s} ≤ dim S ≤ d.
   Dropping the nonnegative degree gives dim O_{Y,y} ≤ d + n.
3. By lem-pc-scheme-dimension-local-rings for Y, dim Y is the supremum of
   its local ring dimensions. Every term is bounded by d + n, so is their
   supremum. No finite cover or separation hypothesis is needed.
-/
theorem generic_residue_transcendence_dimension_bound
    {Y S : Scheme.{u}} (f : Y ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (d n : ℕ)
    (hS : topologicalKrullDim S ≤ (d : WithBot ℕ∞))
    (hgeneric : ∀ (η : Y) (Z : Set Y),
      Z ∈ irreducibleComponents Y → IsGenericPoint η Z →
        @Algebra.trdeg (S.residueField (f η)) (Y.residueField η) _ _
          (f.residueFieldMap η).hom.toAlgebra ≤ (n : Cardinal)) :
    topologicalKrullDim Y ≤ ((d + n : ℕ) : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
