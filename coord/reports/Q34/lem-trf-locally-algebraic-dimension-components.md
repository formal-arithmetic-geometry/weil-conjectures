## Worker report

The module `Sheaf.AlgebraicGeometry.LocallyAlgebraicDimensionComponents` states
`AlgebraicGeometry.topologicalKrullDimAt_eq_max_component_dimension`, with its proof
postponed by `sorry`. It introduces no definitions. The node is unchanged except
for its `lean` field. No new nodes, dependency repairs, or statement correction are needed.

Source read: `literature/stacks-project/varieties.tex`, lines 3782–3810 and
3894–3904: Stacks 0A21, part (5), tagged 0B1B, first equality and its proof.
Only the component-maximum equality is the assigned node; the source's separate
minimum over closed specializations is not asserted by this node.

Hypothesis and clause correspondence:

- Field k: `{k : Type u} [Field k]`.
- Scheme X: `{X : Scheme.{u}}`.
- Spec k and its given structure map: `(f : X ⟶ Spec (.of k))`.
- Locally finite type: `[LocallyOfFiniteType f]`; there is no quasi-compactness
  assumption and thus no restriction to globally finite type schemes.
- Every point x: `(x : X)` is universally quantified by the theorem binder.
- Local topological dimension dim_x X: `topologicalKrullDimAt x`, the recorded
  infimum over dimensions of open neighbourhoods, not the dimension of the stalk.
- Components containing x: `C : Set X`, `C ∈ irreducibleComponents X`, and `x ∈ C`.
- Topological Krull dimension of C with its subspace topology:
  `topologicalKrullDim C`. Coercion of the set to its subtype installs the recorded
  `instTopologicalSpaceSubtype` induced topology.
- The displayed maximum equality is expressed without introducing a chosen
  maximum: the first conjunct says every such C satisfies
  `topologicalKrullDim C ≤ topologicalKrullDimAt x`; the second conjunct supplies
  such a C with `topologicalKrullDim C = topologicalKrullDimAt x`.
  Together they say exactly that the local dimension is the attained maximum.
- Nonemptiness and attainment: the existential in the second conjunct asserts
  both that a component containing x exists and that it attains the value.
- Irreducibility, equidimensionality, separatedness and quasi-compactness of X
  are not hypotheses. Empty X is allowed: the point binder makes the assertion
  vacuous. No finiteness clause beyond the assigned node is added.

All variables and the universe are explicit; `set_option autoImplicit false`
checks that no implicit names are introduced. The scheme category's common
universe for X and Spec k is its standard size convention. There are no
independent test-universe parameters or restrictions on characteristics.

Recorded statement dependencies used (their source signatures and docstrings
were opened):

- `def-weil-field`: `Field` in `Mathlib.Algebra.Field.Defs`, extending
  `CommRing` and `DivisionRing` (including nontriviality).
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`; the locally affine locally ringed space
  and its locally ringed space morphisms.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; its all-affine-pairs condition
  is the recorded equivalent interface for the affine-cover definition.
- `def-kun-topological-dimension-at-point`: `topologicalKrullDimAt` in
  `WeilConjectures.Mathlib.Topology.KrullDimension`, defined by
  `⨅ (U : Opens X) (_ : x ∈ U), topologicalKrullDim U`.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim` in
  `Mathlib.Topology.KrullDimension`, defined as the Krull dimension of
  `IrreducibleCloseds`.
- `def-weil-irreducible-components`: `irreducibleComponents` in
  `Mathlib.Topology.Irreducible`, the maximal `IsIrreducible` subsets.
- `def-kun-subspace-topology`: `instTopologicalSpaceSubtype` in
  `Mathlib.Topology.Defs.Induced`, the topology induced by subtype inclusion.

The three public imports expose these existing declarations (including the
transitive imports of Scheme, Field, global Krull dimension, and subtype topology).
Proof imports retain the recorded proof route: `IsOpen.topologicalKrullDimAt_eq`
from the already public local-dimension module; the irreducible-closed-subset order
isomorphism from `Mathlib.Topology.Sets.Closeds`; closed subscheme construction from
`Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`; closed immersions and their
homeomorphisms from `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`;
locally finite type immersions from `Mathlib.AlgebraicGeometry.Morphisms.Immersion`;
locally finite type composition from the public finite-type module (the clause
used from `lem-weil-pbc-proper-fp-permanence`);
`AlgebraicGeometry.dimension_locally_algebraic` from
`WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic`;
`IsHomeomorph.topologicalKrullDim_eq` from the global Krull-dimension module;
and `AlgebraicGeometry.dimension_at_point_components` from
`WeilConjectures.RingTheory.DimensionAtPointComponents`.
The docstring gives all four DAG proof steps and names their dependencies.

Edge cases checked before writing:

- Empty scheme: no x can be supplied; no spurious global nonempty assumption.
- Spec of a field: one component, both dimensions zero.
- Generic points: the local topological dimension of an irreducible variety is
  its global dimension; a stalk-height interpretation would be wrong here.
- A line and a plane meeting at a point: the local dimension at the intersection
  is two; there is no requirement that both components have that dimension.
- Nonreduced finite type schemes: component subsets and dimensions are
  topological; no reducedness is imposed.
- Infinite disjoint union of affine spaces of increasing dimensions: global
  dimension can be infinite; at each point the finite maximum over components
  through that point remains the relevant quantity. No global bound is imposed.
- Arbitrary characteristic and nonseparated schemes are admitted unchanged.

Searches for an existing statement, 2026-10-24:

- `msearch.py ... leanfinder`: "For a scheme locally of finite type over a field
  the local topological dimension at a point is the maximum of dimensions of
  irreducible components containing it". Eight results: Artinian dimension-zero
  criteria, closed-point height, finite type at closed points, quasi-sobriety,
  integral-space order, rank at stalk, finite morphisms and the function-field
  instance. None is the component maximum formula.
- `msearch.py ... loogle "topologicalKrullDim, irreducibleComponents"`: zero hits.
- `msearch.py ... grep "topologicalKrullDimAt|topologicalKrullDim.*irreducibleComponents"`:
  zero Mathlib hits.
- `msearch.py ... leansearch`: "Local topological dimension of a locally finite
  type scheme over a field is the maximum of irreducible component dimensions
  through the point". Eight results, including `topologicalKrullDim`, existence
  of a component, locally finite presentation implies locally finite type,
  closed-point height and local affine neighbourhoods; none states this theorem.
- `rg -n` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `topologicalKrullDimAt`, dimension/component combinations, and
  `dimension_at_point_components`: the existing affine theorem, the
  irreducible locally algebraic theorem, equidimensional-open results, and
  constant-local-dimension criteria have different statements and hypotheses.
  Their source signatures were inspected; none is this arbitrary-component
  locally algebraic maximum formula.
- `grep -rn "lem-trf-locally-algebraic-dimension-components" lean/WeilConjectures`:
  no upstream declaration carrying this node identifier.

No statement dispute or source fault was found.

## Second reading by Q34

A separate final rereading of the node and the completed module checked the
binders against every hypothesis and the two conjuncts against every clause.
The supplied structure morphism and its locally finite type instance are exactly
the node's data. The universal bound plus an equality witness is equivalent to
the specified maximum, including nonemptiness and attainment. Component
membership is maximal irreducibility in X, and dimensions use the actual subtype
topology. No condition is imposed on the other components, on global dimension,
on reducedness, or on quasi-compactness. The empty scheme stays vacuous and the
generic-point case uses neighbourhood dimension rather than stalk dimension.
The proof docstring follows all four source-based DAG steps. No mismatch or
mathematical change was found. This rereading was performed in this worker
session; the maintainer's independent delivery review remains separate.
