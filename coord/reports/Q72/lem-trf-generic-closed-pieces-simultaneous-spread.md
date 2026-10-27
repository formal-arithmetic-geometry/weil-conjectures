## Worker report

The module `Sheaf.AlgebraicGeometry.GenericClosedPiecesSimultaneousSpread` states
`AlgebraicGeometry.exists_open_fibre_closed_pieces_dense_complements`, with `sorry`.
It introduces no definitions. The node is unchanged except for its `lean` record.
The source is Stacks `more-morphisms.tex`, Tag 0554, the proof's simultaneous
shrinkings after introducing the closed pieces and their pairwise intersections.
I also read Tags 054X and 054Y in that file and the dependency declarations below.

Hypotheses, clause by clause:

- Schemes and the given morphism are `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Finite type of f is `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the
  conjunction recorded by `def-weil-finite-type-morphism`.
- Irreducibility of Y is `hY : IsIrreducible (Set.univ : Set Y)`.
- The generic point of all of Y is `(η : Y)` with
  `hη : IsGenericPoint η (Set.univ : Set Y)`.
- The finite index set is `(I : Type v) [Finite I]`. There is no nonempty
  assumption and the index universe is independent of the scheme universe.
- The supplied schemes and closed immersions are `Z : I → Scheme.{u}`,
  `j : ∀ i : I, Z i ⟶ X` and `[∀ i : I, IsClosedImmersion (j i)]`.
- The given finite type condition on h_i = f composed with j_i is
  `[∀ i : I, LocallyOfFiniteType (j i ≫ f)]` and
  `[∀ i : I, QuasiCompact (j i ≫ f)]`. Categorical composition has the order
  j_i followed by f, as required. No arbitrary replacement morphism is used.
- D_i is rendered directly by `Set.range (j i)`. D_{i,t} is rendered directly
  by `(f.fiberι t) ⁻¹' Set.range (j i)`, a subset of the actual ordinary
  scheme-theoretic fibre `f.fiber t`, not a geometric fibre or a new model.
- Generic nonemptiness and irreducibility are together `hpieces`, using
  `IsIrreducible ((f.fiberι η) ⁻¹' Set.range (j i))` for each i. Mathlib's
  `IsIrreducible` includes nonemptiness. Closedness of these generic pieces
  already follows from closed immersion and continuity, as in the node.
- The generic covering is `hcover`, the indexed union of those generic
  subsets being `Set.univ` in `f.fiber η`.
- Generic pairwise incomparability is `hincomparable`: for every ordered
  pair i, k with `i ≠ k`, the first generic subset is not contained in the
  second. It is not replaced by mere inequality of the subsets.

Conclusion, clause by clause:

- `∃ V : Y.Opens, η ∈ V` is an open neighbourhood of the specified generic
  point. Membership, rather than just nonemptiness, is retained.
- `∀ t : Y, t ∈ V →` quantifies over every ordinary point in this open.
- The first conjunct states both `IsClosed` and `.Nonempty` for every
  D_{i,t} inside `f.fiber t`.
- The second conjunct says their indexed union equals `Set.univ`, exactly
  the covering of `X_t`.
- The third conjunct is for every ordered distinct pair. It uses
  `Dense {x : (f.fiberι t) ⁻¹' Set.range (j i) |
  (x : f.fiber t) ∉ (f.fiberι t) ⁻¹' Set.range (j k)}`.
  Its ambient space is the subtype D_{i,t} with its induced topology.
  Thus its closure is all of D_{i,t}, exactly the requested relative
  density. Since D_{k,t} is closed by the first conjunct, this subset is
  relatively open as described by the node. There is no assertion of
  density in all of X_t, or of irreducibility of D_{i,t}.
- No Noetherian, separated, flat, or reduced condition is present.

Dependencies used (full source signatures and docstrings were read):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  `AlgebraicGeometry.QuasiCompact`.
- `def-weil-irreducible-components` is a Mathlib leaf. Its `mathlib_match`
  explicitly identifies `IsIrreducible` in `Mathlib.Topology.Irreducible`
  as the subset notion used to define `irreducibleComponents`.
  The statement uses that definition directly, requiring no record repair.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint`.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber` and
  `AlgebraicGeometry.Scheme.Hom.fiberι`.
- Proof-only imports are the three recorded modules:
  `WeilConjectures.AlgebraicGeometry.GenericClosedSubsetFibreNonempty`
  (`AlgebraicGeometry.exists_open_closed_subset_fibre_nonempty`),
  `WeilConjectures.AlgebraicGeometry.GenericFibreClosedCoverSpread`
  (`AlgebraicGeometry.exists_open_generic_fibre_closed_cover`), and
  `WeilConjectures.AlgebraicGeometry.GenericOpenFibreDensity`
  (`AlgebraicGeometry.exists_open_fibre_dense_of_generic_dense`).
  All remaining proof dependencies are already public statement imports.
  The declaration docstring carries each of the six proof steps and names
  the three spreading nodes where they are used.

Edge cases checked before writing:

- Empty I: `hpieces` and incomparability are vacuous; the empty indexed
  union in `hcover` equals `Set.univ` exactly when the generic fibre is
  empty. The conclusion then forces every fibre over V to be empty.
  The generic closed-cover spreading dependency covers this case.
- Singleton I: no density condition is imposed; the sole piece is nonempty
  and covers each fibre over V.
- Empty X and empty generic fibre: possible with empty I; a nonempty I is
  excluded by `hpieces`, as the node requires. No global nonempty-X
  assumption has been introduced.
- Empty Y is already excluded by the given point η, not by any new condition.
- Arbitrary finite index types, nonreduced schemes, positive characteristic,
  and reducible specialized pieces remain allowed. All schemes have a
  common arbitrary universe u; any family of differently sized schemes
  can be placed in a common universe. No site or test-object size condition
  is involved.

Searches for an existing statement (2026-10-24, using the prescribed msearch.py;
raw outputs are retained in sandbox `searches.jsonl`):

- LeanFinder: `A finite closed cover of the generic fibre by incomparable
  irreducible pieces spreads to nonempty covering fibres with dense pairwise
  relative complements`. Eight hits, including affine-transition-limit
  covers, `genericPoints.finite`, Proj covers, and finite open subcovers;
  none states this finite closed-family spreading assertion.
- Loogle: `"fiber", "Dense"`. The sole hit is
  `IsPreirreducible.preimage_of_dense_isPreirreducible_fiber`: this is an
  open-map criterion for irreducibility of a preimage and supplies no base
  neighbourhood or supplied closed-family conclusion.
- Mathlib grep in AlgebraicGeometry:
  `(generic|fiber|fibre).*(dense|nowhere|cover)|(dense|nowhere|cover).*(generic|fiber|fibre)`.
  Four hits concern quasi-finite fibre open covers and rational-map domains;
  none is the requested statement.
- LeanSearch: `Finite closed generic fibre cover spreads to nonempty covering
  fibres with dense pairwise differences`. Eight hits concern covering maps,
  cover-dense functors, finite fibres, dense sets after removing finite sets,
  and DenseRange. None gives this assertion.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `(generic|fibre|fiber).*(pieces|closed.cover|simultaneous)|simultaneous.*(spread|closed)|closedPieces`.
  Read the closest results: `GenericFibreComponentSpread.lean` states clopen
  spreading of one connected component; `GenericFibreComponentLowerBound.lean`
  states a lower bound on the number of components. Neither states this
  assertion about the supplied finite family. The three spreading lemmas
  are already recorded proof dependencies, not exact matches.
- `grep -rn` for the exact item id in `lean/WeilConjectures`: no result.
- Name searches in Mathlib, `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for
  `exists_open_fibre_closed_pieces_dense_complements`: no existing declaration.

No statement correction, disputed statement, new node, or dependency module is needed.
Validation: the prescribed scompile.py compiled this module in both sandbox and
library module modes without errors or non-sorry warnings.

## Second reading by Q72

This is the author's second reading; the maintainer supplies the independent review,
as required by the dispatch brief. I reopened the node and the final signature and
matched every hypothesis and conclusion as listed above. In particular I checked
that both finite type hypotheses are conjunctions of locally finite type and
quasi-compactness; the density subtype is the first piece, not the whole fibre;
the negative subset relation is for ordered distinct indices; the union is the
whole ordinary fibre; and finite I has no nonempty assumption. The point η belongs
to the returned open. Nonemptiness is included in generic `IsIrreducible` and is
explicit in the specialized conclusion. No mismatch was found and no changes to
the mathematical statement were made. All variables and universes are explicitly
bound and `autoImplicit` is disabled. The sole postponed theorem is the item itself.
