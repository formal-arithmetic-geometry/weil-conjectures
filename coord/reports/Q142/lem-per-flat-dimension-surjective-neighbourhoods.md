## Worker report

The module `Sheaf.AlgebraicGeometry.FlatDimensionSurjectiveNeighbourhoods` states
`AlgebraicGeometry.exists_surjective_dimension_attaining_neighbourhoods_of_flat`.
It has one theorem with proof `sorry`, no definitions and no auxiliary claims.
The node is unchanged except for its `lean` record.

I read the node's statement, all six statement-dependency nodes and their recorded
interfaces, all proof-dependency records, and Stacks `morphisms.tex`, Tag 0AFE,
`lemma-rel-dimension-dimension`, especially its first proof paragraph. That paragraph
first attains the two local dimensions, then uses openness to shrink the target to
the image. The node expands precisely this neighbourhood construction and does not
assert the final dimension formula of 0AFE.

Clause-by-clause rendering:

- The schemes and their morphism are `{X Y : Scheme.{u}}` and `(f : X ⟶ Y)`.
  The explicit universe `u` is arbitrary. The category of schemes uses a common
  universe, as do the dependency interfaces.
- Local Noetherianity of both schemes is `[IsLocallyNoetherian X]` and
  `[IsLocallyNoetherian Y]`. Flatness is `[Flat f]` and local finite type is
  `[LocallyOfFiniteType f]`. No quasi-compactness, separatedness, finite global
  presentation, nonemptiness or finite-dimensionality hypothesis is imposed.
- The natural number is `(d : ℕ)`. The hypothesis at every source point is
  `hd : ∀ a : X, topologicalKrullDimAt (f.asFiber a) = (d : WithBot ℕ∞)`.
  `f.asFiber a` is the canonical point of the actual scheme-theoretic fibre
  `f.fiber (f a)`, using its homeomorphism with the topological fibre. This is
  local topological dimension, not the Krull dimension of the local ring.
- The chosen point is `(x : X)` and the image point is the term `f x`.
- Open subschemes are `U : X.Opens` and `V : Y.Opens`, with the canonical scheme
  structures `U.toScheme` and `V.toScheme`. The clauses `x ∈ U` and `f x ∈ V`
  give both required neighbourhood conditions.
- The equality `f '' (U : Set X) = (V : Set Y)` is exactly `f(U) = V`.
- `topologicalKrullDim U.toScheme = topologicalKrullDimAt x` and
  `topologicalKrullDim V.toScheme = topologicalKrullDimAt (f x)` give the two
  dimension-attainment equalities.
- The existential `e : U ≤ f ⁻¹ᵁ V` makes the canonical restricted morphism
  `f.resLE V U e : U.toScheme ⟶ V.toScheme` well typed. This is restriction of
  the original scheme morphism, not a freely chosen map; the image equality
  already implies the containment supplied by `e`.
- `Surjective (f.resLE V U e)`, `Flat (f.resLE V U e)` and
  `LocallyOfFiniteType (f.resLE V U e)` give precisely the restricted morphism's
  three asserted properties. `Surjective` is the scheme-morphism class, whose
  field is surjectivity of the underlying map.
- `IsLocallyNoetherian U.toScheme` and `IsLocallyNoetherian V.toScheme` state the
  two asserted properties of the open schemes.
- Finally `∀ a : U.toScheme, topologicalKrullDimAt
  ((f.resLE V U e).asFiber a) = (d : WithBot ℕ∞)` states the same local fibre
  dimension for every point of the restricted source, using the scheme fibre
  over its image in V. No relation between the two global dimensions is added.

Dependency declarations used, with full signatures and docstrings inspected:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`,
  the all-affine-open definition equivalent to the recorded affine-cover notion;
  also `IsLocallyNoetherian.component_noetherian`,
  `isLocallyNoetherian_of_affine_cover`, and
  `LocallyOfFinitePresentation.iff_locallyOfFiniteType` for the proof plan.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, together
  with `Flat.iff_flat_stalkMap`, which identifies it with the node's stalkwise
  flatness condition.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` and its generated
  `locallyOfFiniteType_iff`, the recorded all-affine-pairs formulation.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber`,
  `fiberι`, `fiberToSpecResidueField`, `fiberHomeo`, and `asFiber`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`
  and `IsOpen.topologicalKrullDimAt_eq`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim` and
  `Topology.IsInducing.topologicalKrullDim_le`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  the open-subscheme/restriction infrastructure exposes `Scheme.Hom.resLE` from
  `Mathlib.AlgebraicGeometry.Restrict`. I read that definition: it is the open
  inclusion into the preimage followed by the target restriction.
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`:
  `AlgebraicGeometry.UniversallyOpen.of_flat` for the openness proof dependency.

The imports of statement dependencies are public. Additional modules belonging
only to the proof plan are plain imports; shared modules already imported publicly
are not repeated privately. The theorem docstring expands all six DAG proof steps
and names their dependency nodes. No proof import from a downstream dimension
formula is used.

Edge cases checked mathematically before writing: an empty X leaves no point x and
hence gives a vacuous universally quantified claim; an empty Y permits only empty
X. The binder `d : ℕ` allows zero. Infinite local dimension on X or Y remains
available in `WithBot ℕ∞`; there is no natural-number bound on those dimensions.
An originally nonsurjective map is allowed because surjectivity is asserted only
for the restricted map onto its open image. The identity map permits d = 0 and
ordinary dimension-attaining opens. The projection of affine d-space over a
locally Noetherian base matches the positive-dimension case. There is no
restriction on characteristic. In particular the source and target are not
assumed affine or globally Noetherian.

Searches actually run through `msearch.py` (logged in `searches.jsonl`):

- LeanFinder: “A flat locally finite type morphism of locally Noetherian schemes
  has surjective open restrictions around each point attaining local Krull
  dimensions and preserving fibre dimension”: eight results, including
  `UniversallyOpen.of_flat`, `LocallyOfFiniteType.isLocallyNoetherian`,
  `Flat.generalizingMap`, `Flat`, and `LocallyOfFiniteType`; these are individual
  ingredients, not this full existential statement.
- Loogle: `"topologicalKrullDimAt", "Flat"`: zero results.
- Mathlib grep: `(krullDimAt|KrullDimAt).*(surject|neighb)|(surject|neighb).*(krullDimAt|KrullDimAt)`:
  zero results.
- LeanSearch: “An open morphism admits surjective open neighbourhood restrictions
  attaining local Krull dimensions”: eight results, including
  `topologicalKrullDim`, `IsOpenCover.isOpenMap_iff_restrictPreimage`,
  `IsHomeomorph.topologicalKrullDim_eq` and finite-type open immersions;
  no exact match.

Also searched `lean/WeilConjectures`, `lean/Sheaf` and
`dag/lean_names_upstream.json` with rg for this node id, surjective neighbourhoods,
`topologicalKrullDimAt`, and dimension-existence patterns. The exact node-id
search in WeilConjectures had no hit. Nearby declarations were inspected: the
parent `FlatConstantRelativeDimension` states the final local dimension formula,
not this neighbourhood statement, and `FiniteTypeFibreDimensionBound` has fibre
restriction invariance and bounds, not simultaneous dimension-attaining opens.
Existing notions were reused throughout; no new or repaired dependency nodes
are needed. No statement fault or disputed clause was found.

Validation: scompile.py compiled this module on the server against the live
published library, with no errors or warnings. The proof remains `sorry` as
required for stage 2. The standard deliver2.py dry run and delivery follow.

## Second reading by Q142

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
