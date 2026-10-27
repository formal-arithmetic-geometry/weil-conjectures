## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiFiniteSourceDimension` states
`AlgebraicGeometry.AlgebraicSpace.topologicalKrullDim_source_le_of_locallyQuasiFinite`,
with the whole proof `sorry`. It adds no definitions and leaves the node statement unchanged.

Clause-by-clause reading:

- A scheme S is the explicitly bound `{S : Scheme.{u}}`.
- An algebraic space X over S is `(X : AlgebraicSpace S)`, the existing full subcategory
  of fppf sheaves with representable diagonal and a surjective etale scheme atlas.
- An S-scheme U is `(U : Over S)`; its underlying scheme is `U.left`.
- The S-morphism f is `(f : yoneda.obj U ⟶ X.obj.obj)`, a natural transformation of
  the functors of points on schemes over S. Representability is `(hf : IsRepresentable f)`.
- Quasi-separatedness is `hqs : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left)
  (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj))`. Products of presheaves on Over S are relative
  products over S. This is exactly quasi-compactness of the diagonal on all scheme tests;
  the scheme predicate means compact inverse images of compact opens. This does not assume
  quasi-separatedness of S or U, nor replace the relative diagonal by an absolute one.
- Chartwise local quasi-finiteness is `hqf`: for every S-scheme V and every `a : h_V ⟶ X`,
  `IsEtale a` implies existence of W, its scheme projection `p : W ⟶ V`, and its map
  `q : h_W ⟶ h_U`, with `IsPullback q (yoneda.map p) f a` and
  `p.left.IsLocallyQuasiFinite`. The pullback square represents precisely the sheaf
  fibre product U ×_X V. Existence of such a representation is equivalent to the property
  for the represented scheme projection, since representations are uniquely isomorphic.
  The predicate is the recorded Stacks notion, including local finite type.
- The conclusion is `topologicalKrullDim U.left ≤ topologicalKrullDim (Point X.obj.obj)`.
  The latter point type has the existing `pointTopologicalSpace` instance, final for all
  representable etale scheme charts. Both dimensions lie in `WithBot ℕ∞`, with bottom -∞.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`, and `IsEtale`. Their full
  definitions supply the representability, diagonal and chart interfaces used here.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`, defined pointwise using
  `IsQuasiFiniteAtPoint` (affine finite-type/quasi-finite-at-prime tests).
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`, using
  `Point` and `schemePointMap` from `AlgebraicSpacePointClasses`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim` is the order dimension of
  irreducible closed subsets.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- The available proof dependency `lem-pc-scheme-dimension-local-rings` is imported privately
  as `WeilConjectures.AlgebraicGeometry.Dimension` (`Scheme.dim_eq_topologicalKrullDim`).
  The other two proof dependencies, `lem-sfb-space-topological-dimension-local-rings` and
  `lem-sfb-space-local-ring-dimension-quasifinite`, have no Lean record in the read clone;
  their intended uses are included step by step in the theorem docstring. They are not
  needed to type this statement and no replacement statements are introduced.

Source and edge-case checks:
Read `literature/stacks-project/decent-spaces.tex`,
`lemma-dimension-local-ring-quasi-finite`, `lemma-dimension-quasi-finite`, and
`lemma-dimension-decent-space`. The source compares local-ring dimensions and then takes
suprema; it does not require source quasi-separatedness, global finite type, Noetherianity,
finite dimension, or surjectivity. Empty U gives bottom on the left. Empty X forces empty U,
so both dimensions are bottom. Infinite dimension is allowed on either side. Arbitrary base
schemes are retained; there is no independent smaller universe for the test schemes.
The `Over S` universe agrees with the recorded algebraic-space site.

Searches (2026-10-24):

- msearch LeanFinder: "A scheme locally quasi-finite over a quasi-separated algebraic space
  has topological Krull dimension at most that of the algebraic space". Eight hits, all
  scheme-only properties or local Artinian consequences; no algebraic-space bound.
- msearch LeanSearch: "The topological dimension of a scheme locally quasi-finite over a
  quasi-separated algebraic space is bounded by the dimension of that algebraic space".
  Eight hits, scheme quasi-finiteness and quasi-separatedness; no exact statement.
- msearch Loogle: `"AlgebraicSpace", "dimension"`: zero hits.
- msearch Mathlib grep: `quasi.?[Ff]inite.*[Dd]im|[Dd]im.*quasi.?[Ff]inite`: one incidental
  Zariski Main Theorem hit; no statement about algebraic spaces.
- rg with the same dimension/quasi-finiteness pattern in `lean/WeilConjectures` and
  `lean/Sheaf`: found scheme-only dimension inequalities, local ring lemmas, and consumer
  docstrings naming this item. None states this algebraic-space inequality.
- `grep -rn` of the item id in `lean/WeilConjectures`: no hits. Searching
  `dag/lean_names_upstream.json` with the dimension/quasi-finiteness pattern: no hits.
- Inspection of `AlgebraicSpaceAbsoluteQuasiSeparated` and `AlgebraicSpaceAffineQuasiFinite`
  confirmed that they concern an absolute affine-test criterion and globally finite-type
  finite geometric fibres respectively; neither replaces this node's relative diagonal
  condition or its locally quasi-finite scheme projection condition.

No statement correction, disputed assertion, new node, or dependency repair is required.
All writes are confined to the assigned sandbox; all compiles use scompile.py.

## Second reading by Q23

The dispatcher forbids starting another agent; this is a separate second pass by the same
worker, with both the JSON statement and final Lean file open, followed by the maintainer's
independent review. S, X, U and f match the named objects. `hf` preserves the explicitly
stated representability hypothesis. `hqs` tests the relative diagonal with the exact
quasi-compact scheme-morphism predicate, imposing no absolute base condition. `hqf` quantifies
over every etale chart, and its pullback square has q to U and p to V, so the quasi-finiteness
predicate is on the correct projection. It uses the recorded Stacks finite-type-inclusive
predicate. The conclusion uses U's scheme topology and X's recorded atlas topology, with
bottom and infinity retained. No mismatches were found and no changes were needed.
