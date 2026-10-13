module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # Local dimension of an equidimensional open in a locally algebraic scheme

Source: Stacks Project, Tag 0A21 (3), (5).
(blueprint: lem-sbc-equidimensional-open-local-dimension)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- Pure dimension of an open in a locally algebraic scheme gives its local dimension.

Source: Stacks Project, Tag 0A21 (3), (5).
Proof: The open subscheme O is locally of finite type over k. At a point x of O,
Tag 0A21 (5) identifies its local dimension with the maximum of the dimensions of
irreducible components of O containing x. There is at least one such component
(the irreducible component of x), and every such dimension is n by hdim, so this
maximum is n. More explicitly, choose an affine neighbourhood A of x in O.
Components of A through x correspond to components of O through x by intersection.
Tag 0A21 (3) preserves component dimension on these nonempty open intersections;
the finite-type affine formula of Tag 0A21 (5) therefore gives n at x in A.
Local dimension is preserved by open inclusions, first from A to O and then from
O to Y, using IsOpen.topologicalKrullDimAt_eq. Empty O has no points, so the
statement is vacuous; no global finite-type or quasi-compact hypothesis is needed.
(blueprint: lem-sbc-equidimensional-open-local-dimension) -/
theorem topologicalKrullDimAt_eq_of_equidimensional_open
    {k : Type u} [Field k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType g] (O : Y.Opens) (n : ℕ)
    (hdim : ∀ C ∈ irreducibleComponents ↥O, topologicalKrullDim C = (n : WithBot ℕ∞))
    (x : Y) (hx : x ∈ O) : topologicalKrullDimAt x = (n : WithBot ℕ∞) := by sorry

end AlgebraicGeometry
