## Worker report

The module `lean/Sheaf/AlgebraicGeometry/NowhereDenseDimensionDrop.lean` states
`AlgebraicGeometry.Scheme.topologicalKrullDim_lt_of_isNowhereDense`, with a single
`sorry` proof and no new definitions. The node copy changes only `lean`.

Hypothesis and conclusion correspondence:

- A scheme X: `(X : Scheme.{u})`, for explicitly bound arbitrary universe `u`.
- Nonempty X: `[Nonempty X]`, referring to its underlying point type.
- Locally Noetherian X: `[IsLocallyNoetherian X]`, exactly the recorded declaration
  of `pqf-def-locnoeth`. The Mathlib affine-cover equivalence already identifies
  its every-affine-open presentation with the node's affine-cover presentation.
- Finite dimension d: `(d : ℕ)` and
  `(hX : topologicalKrullDim X = (d : WithBot ℕ∞))`. Natural-number d covers all
  possible finite dimensions of nonempty X; it excludes precisely infinity and bottom.
- A subset Z of X: `(Z : Set X)`, without any chosen scheme structure.
- Closed Z: `(hZ : IsClosed Z)`.
- Nowhere dense Z: `(hnow : IsNowhereDense Z)`. Mathlib defines this by
  `interior (closure Z) = ∅`, equivalent for closed Z to empty interior.
- Strict dimension drop: `topologicalKrullDim Z < (d : WithBot ℕ∞)`.
  Here Z coerces to its subtype with the induced topology, exactly the recorded
  subset-dimension convention of `def-kun-topological-krull-dimension`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsLocallyNoetherian`:
  class with `component_noetherian : ∀ U : X.affineOpens, IsNoetherianRing Γ(X,U)`.
  Also read its affine-cover characterizations and open-immersion preservation.
- `Mathlib.Topology.KrullDimension`, `topologicalKrullDim` (the dimension node's
  `mathlib_match` and recorded `lean`): `Order.krullDim (IrreducibleCloseds T)` in
  `WithBot ℕ∞`, the supremum of strict-chain lengths.
- `Mathlib.Topology.GDelta.Basic`, `IsNowhereDense`, the existing Mathlib predicate.

The declaration docstring carries all three natural-language proof steps, including
component containment, local finiteness and strict containment, chain extension,
and the supremum and dimension-zero cases. No proof dependencies are imported merely
to mention them in the docstring.

Edge cases checked before writing: Z empty has dimension bottom, strictly below every
natural d, including zero. For d = 0 any nonempty Z would supply an irreducible component
properly contained in a component of X, a forbidden length-one chain. Reducible and
non-quasi-compact locally Noetherian X are included; no global Noetherian, integral,
finite-type, equidimensional, field, or characteristic restriction was added. Empty X
is explicitly excluded by the node itself. Infinite-dimensional X is excluded by hX,
as required. All binders and universes are explicit. No statement fault or correction.

Source read: [Stacks Tag 02P2](https://stacks.math.columbia.edu/tag/02P2).
It supplies the nowhere-dense closed support in the Hilbert argument; the general
finite-dimensional dimension argument is the agent-origin proof recorded in this node,
not a separate dimension theorem asserted in Tag 02P2. The local literature checkout
is absent on this machine, so the source tag was read online.

Searches (executed through msearch.py, recorded in searches.jsonl):

- LeanFinder: “A nowhere dense closed subset of a nonempty finite dimensional locally
  Noetherian scheme has strictly smaller topological Krull dimension”: eight hits,
  including `topologicalKrullDim_subspace_le`, the definition, Artinian dimension-zero
  characterization, and ring-dimension results. No strict-drop match.
- Loogle: `topologicalKrullDim, IsNowhereDense`: zero hits.
- Mathlib grep: `nowhereDense|nowhere_dense|nowhere dense.*dimension`: nine hits,
  defining or using nowhere density; no dimension-drop statement.
- LeanSearch: “A nowhere dense closed subset of a finite dimensional locally Noetherian
  scheme has strictly smaller Krull dimension”: unavailable, Internal Server Error.
- Source rg: `IsNowhereDense|nowhere.dense|nowhereDense` in WeilConjectures found only
  `Topology/StratificationDense.lean`, about finite unions and locally closed strata.
  rg for this item's exact blueprint id found no occurrence.
- Project rg for dimension and nowhere density found only the dimension-at-most-one
  specialization `NowhereDenseDimZero.lean` and descriptive mentions. That specialization
  requires finite type over a field and a closed subscheme, and is not this statement.
- Full chosen declaration name searched in Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no collision.

Server single-file compilation completed successfully in 1.7 seconds, exit code zero,
with no errors or warnings. No local compilation was performed.

## Second reading by G1

I independently opened the item node, its delivered module, both statement-dependency
nodes and their actual Mathlib declarations. The complete object/hypothesis/conclusion
list, in the order of the node, is:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Scheme X | `(X : Scheme.{u})` | Exact; Mathlib Scheme is a locally ringed space locally affine, and its CoeSort is its underlying point carrier. |
| X nonempty | `[Nonempty X]` | Exact nonemptiness of the point carrier, not an affine or integral assumption. |
| X locally Noetherian | `[IsLocallyNoetherian X]` | Exact recorded pqf-def-locnoeth notion. The class checks every affine open; `isLocallyNoetherian_of_affine_cover` and `isLocallyNoetherian_iff_of_affine_openCover` give the already-proved equivalence with the node's existence of an affine Noetherian cover. |
| Finite dimension d | `(d : ℕ)` and `(hX : topologicalKrullDim X = (d : WithBot ℕ∞))` | Exact. For nonempty X a finite dimension is a natural number; bottom and infinity are excluded exactly as the node requires. |
| Subset Z of X | `(Z : Set X)` | Exact arbitrary subset, with no extra scheme structure or morphism. |
| Z closed | `(hZ : IsClosed Z)` | Exact closedness in the ambient X. |
| Z nowhere dense | `(hnow : IsNowhereDense Z)` | Exact Mathlib predicate `interior (closure Z) = ∅`; since Z is closed this is empty interior. |
| Strict dimension drop | `topologicalKrullDim Z < (d : WithBot ℕ∞)` | Exact sole conclusion, with Z coerced to its subtype and the induced topology. Quantification is over every such X, d and Z. |

For the dimension dependency I also read `IrreducibleCloseds` (nonempty irreducible
closed subsets, ordered by inclusion), `IsIrreducible` (explicitly nonempty), and
`Order.krullDim` (supremum of LTSeries lengths). Thus the notation measures exactly
chains with n strict inclusions, not cardinality of chains or a shifted dimension.
All declarations and universe u are bound; there are no ambient section assumptions.

Source reading: the local literature tree contains no Stacks .tex checkout. I read
actual upstream divisors.tex, section `section-meromorphic-noetherian`, and
`lemma-make-maps-regular-section` (Tag 02P2), including its preceding section text.
The section assumes locally Noetherian schemes, with no field, characteristic,
separatedness, quasi-compactness or global Noetherian assumption throughout.
Tag 02P2 supplies a nowhere-dense closed support; its invertible module, meromorphic
section and coherent module construct that support and are not assumptions of this
generic dimension lemma. As the node's source and proof_origin explicitly say, the
dimension implication is the agent-origin finite-dimensional component argument,
not a theorem literally stated by 02P2. Sources inspected:
[divisors.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/divisors.tex),
[Tag 02P2](https://stacks.math.columbia.edu/tag/02P2).

Edge cases: empty X is intentionally excluded by the node and Lean alike. Z may be
empty: its dimension is bottom, strictly below every natural d, including zero.
For d = 0, any nonempty irreducible component C of Z must be properly contained in
a component W of X; this gives a forbidden chain of length one, so Z must be empty.
The zero ring yields an empty affine scheme and is excluded only by nonempty X.
Reducible schemes, nilpotents, infinitely many locally finite components and
non-quasi-compact schemes remain allowed. There is no index-set finiteness binder,
no characteristic restriction and no restriction on the explicitly arbitrary u.

Independent searches, using different wording from the first worker and recorded
through msearch.py in searches.jsonl:

- LeanFinder: "A closed subset with empty interior in a locally Noetherian space has
  lower Krull dimension" returned eight hits: subspace monotonicity, the dimension
  definition, locally Artinian dimension-zero characterization and ring comparisons;
  none states this strict drop.
- Loogle: `topologicalKrullDim, IsClosed` returned zero hits.
- Mathlib grep: `KrullDim.*(lt|interior)|isNowhereDense.*[Dd]im|[Dd]im.*isNowhereDense`
  returned 17 order/ring dimension hits, none this statement.
- LeanSearch: "Closed subsets avoiding every irreducible component of a locally
  Noetherian scheme have lower finite Krull dimension" was unavailable (Internal
  Server Error); this is recorded as unavailable rather than a negative result.
- Independent rg of the source WeilConjectures tree and project lean/Sheaf for
  `dimension.*(dense|interior)|[Kk]rull.*(dense|interior)|isNowhereDense|IsNowhereDense`
  found the source `WeilConjectures/Mathlib/Topology/KrullDimension.lean`. I read
  that entire module: its dense-open complement results require an irreducible
  space of dimension at most one, and its inducing-map surjectivity theorem also
  requires irreducibility; neither states the arbitrary locally Noetherian scheme
  assertion here. I also opened the project's NowhereDenseDimZero.lean: it has
  a finite-type-over-a-field hypothesis, dimension at most one and a closed
  subscheme, so it is a specialization rather than an existing exact match.
- The full declaration name and exact blueprint id have no hit in Mathlib,
  WeilConjectures, lean/Sheaf or dag/lean_names_upstream.json.

No new definition nodes or dependency modules were delivered, and none is missing.
No statement_change is present or required. I found no mismatch and preserved the
Lean and node record unchanged. The module and theorem docstrings carry the source
and blueprint id; the theorem docstring follows all three node proof steps:
empty case and component containment, local finiteness and strict containment with
chain extension, and the supremum conclusion with the separate d = 0 argument.
There is exactly one theorem with proof `by sorry`, no definitions and no proofs
added. All three imports supply notions actually used in the signature.
I verified the node's lean.statement is character-for-character equal to the file
signature and every Lean line is at most 100 characters. Server single-file
compilation via scompile.py succeeded with exit code zero and no warnings.
