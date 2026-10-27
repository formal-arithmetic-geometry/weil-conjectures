## Worker report

The module `Sheaf.AlgebraicGeometry.CodimensionOnePointsAffineNeighbourhood` states
`AlgebraicGeometry.exists_isAffineOpen_containing_codimensionOne_points`, with its sole
proof `sorry`. It introduces no definition and changes only the item's `lean` field.
The source was read directly in `literature/stacks-project/varieties.tex`, lines 9141–9156,
Tag 09NN. Its hypotheses and conclusion agree with the node; no correction is needed.

Clause-by-clause rendering:

- A scheme Z: `(Z : Scheme.{u})`, in an arbitrary explicitly bound universe `u`.
- Separatedness: `[Z.IsSeparated]`, Mathlib's absolute separatedness class, defined
  as separatedness of the structure morphism to the terminal scheme; equivalently
  its absolute diagonal is a closed immersion.
- Every quasi-compact open subscheme has finitely many irreducible components:
  `hcomponents : ∀ U : Z.Opens, IsCompact (U : Set Z) →
  (irreducibleComponents U).Finite`. `IsCompact` is quasi-compactness without a
  Hausdorff hypothesis. The type `U` has the subspace topology, so these components
  are those of the open subscheme, rather than components of Z meeting U.
- The list z_1,...,z_r with r >= 0: `(r : ℕ) (z : Fin r → Z)`.
  No distinctness or positivity condition is imposed.
- Every selected local ring is Noetherian:
  `hnoetherian : ∀ i : Fin r, IsNoetherianRing (Z.presheaf.stalk (z i))`.
- Every selected local ring has Krull dimension at most one:
  `hdimension : ∀ i : Fin r, ringKrullDim (Z.presheaf.stalk (z i)) ≤ 1`.
  The value of `ringKrullDim` is `WithBot ℕ∞`, so 1 is the correct bound.
- There is an affine open subscheme U: `∃ U : Z.Opens, IsAffineOpen U ∧ ...`.
  `IsAffineOpen U` is `IsAffine U.toScheme`, defined by the canonical morphism to
  Spec of global sections being an isomorphism. Thus it says exactly that the open
  subscheme is isomorphic to a ring spectrum.
- U contains every selected point: `∀ i : Fin r, z i ∈ U`.
- The empty family is allowed: `Fin 0` is empty and there is no nonemptiness condition
  on U. The empty open, affine as Spec of the zero ring, satisfies the conclusion.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Spec` (def-pc-scheme, def-weil-affine-spectrum).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: exports `AlgebraicGeometry.IsSeparated`;
  the scheme version `AlgebraicGeometry.Scheme.IsSeparated` is in its public import
  `Mathlib.AlgebraicGeometry.Morphisms.Separated` (def-weil-proper-morphism).
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`
  (def-weil-irreducible-components, a Mathlib leaf without a Lean record).
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`
  (def-weil-pbc-noetherian-ring).
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`
  (def-weil-pbc-krull-dimension-ring).
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffineOpen` provides
  the existing affine-open predicate; no second notion was needed.

The proof plan in the theorem docstring follows all five steps of the node, including
passing Noetherianity and the dimension bound through surjections on component stalks.
Plain proof imports preserve the available DAG route:
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` (affine qcqs),
`Mathlib.AlgebraicGeometry.Properties` (integral schemes),
`Mathlib.AlgebraicGeometry.OpenImmersion`,
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` (also base-change stability),
`WeilConjectures.Topology.PresheafModuleStalkFunctor` (module stalks), and
`WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
(`AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`).
The two proof-only nodes `lem-trf-integral-codimension-one-affine-neighbourhood` and
`lem-trf-componentwise-finite-set-affine-neighbourhood` currently have no Lean records
or Mathlib matches, so there are no modules to import for them. They are not notions
needed to type the present statement. No prerequisite or helper is missing from its
statement interface.

Edge cases checked before writing: r = 0; empty Z (only possible with an empty
selection); repeated points; a generic point with dimension-zero field stalk; a DVR
closed point with dimension-one stalk; crossing components, including selection of
an intersection; nonreduced schemes. None is excluded. The hypothesis on compact
opens is retained even when Z is not quasi-compact. No global Noetherianity,
integrality, finite type or base field is assumed.

Searches performed:

- `msearch.py leanfinder` query: "Finite sets of points with Noetherian local rings of
  Krull dimension at most one in a separated scheme have a common affine open
  neighbourhood". Eight hits: local affine neighbourhoods, local Noetherianity,
  affine covers and finite morphisms; none is the finite-set 09NN theorem.
- `msearch.py loogle` query: `AlgebraicGeometry.IsSeparated, "affine"`. Four hits:
  separated/affine morphism permanence and affine locality; no finite-set theorem.
- `msearch.py grep` query:
  `finite.*(points|set).*affine|affine.*(points|set).*finite|codim.*affine`,
  subdirectory `AlgebraicGeometry`. Two hits: `IsAffineOpen.biSup_of_disjoint` and
  the finite-morphism definition; the first requires disjointness and neither matches.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for affine neighbourhoods, 09NN,
  codimension-one affine statements and this node id. The source's
  `AlgebraicGeometry.IsQuasiProjective.exists_isAffineOpen_superset` in
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.AffineNeighbourhood` carries a
  09NN attribute but requires quasi-projectivity over a field: its full statement
  was read and is not this theorem. The generic-point result in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Limits` is also different. The node id
  occurs in the proof docstring of `RelativeNodalPointPinching`, not as a statement.
  `AffineOpenBoundaryCodimensionOne` concerns the boundary of an already affine open.
- `rg` of `dag/lean_names_upstream.json` and both source roots for the proposed name
  `exists_isAffineOpen_containing_codimensionOne_points`: no existing declaration.

No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by Q31

A separate rereading of the node and final signature checked every clause above:
`Scheme.{u}`, `[Z.IsSeparated]`, compactness of each open as a subset of Z and
finiteness of its own component set, arbitrary natural r and indexed points,
Noetherian stalks and `ringKrullDim ≤ 1` only at those points, and an affine open
containing every index. In particular, the finiteness hypothesis is not replaced
by global finite components or locally Noetherianity, and the result does not
require U to be nonempty. No mismatch or consequent edit was found. This is the
worker's second pass; no other agent was started, as required by the dispatch brief.
The maintainer supplies the independent delivery review.
