## Worker report

The module `Sheaf.AlgebraicGeometry.PureDimension` defines
`AlgebraicGeometry.Scheme.IsPureDimension`. It contains one complete Prop-valued definition,
no theorems and no `sorry`. Only the item's `lean` record changes. No new nodes, dependency
modules, statement corrections or disputed statements are needed.

Source checked: `literature/stacks-project/topology.tex`, lines 1468–1473,
Definition 5.10.4 (Tag 0058, `definition-equidimensional`): every irreducible component has
the same dimension. This node fixes that common dimension to a nonnegative integer `d`.

Clause-by-clause correspondence:

- “Let X be a scheme”: `(X : Scheme.{u})`, with the universe `u` declared explicitly.
- “d in Z_{≥0}”: `(d : ℕ)` represents exactly the nonnegative integers.
- “X has pure dimension d (is equidimensional of dimension d) if”: the Prop-valued
  definition `Scheme.IsPureDimension X d` is precisely the following condition, with no
  further hypotheses.
- “Every irreducible component Z of |X|”: `∀ Z : Set X,
  Z ∈ irreducibleComponents X → ...`; the scheme coerces to its underlying space.
- “Z carries the subspace topology”: `topologicalKrullDim Z` takes the subtype of points
  in `Z`, with its induced topology, rather than the dimension of the whole scheme.
- “Krull dimension dim Z = d”: `topologicalKrullDim Z = (d : WithBot ℕ∞)`.
  Mathlib's definition is `Order.krullDim (IrreducibleCloseds Z)`, the supremum of lengths
  of strict chains of nonempty irreducible closed subsets of this same subtype. The cast
  places finite `d` in the dimension type, whose bottom and top also represent minus
  infinity and infinity.
- “The empty scheme has pure dimension d for every d”: the universal condition is
  vacuous when there are no components. There is no `Nonempty X` assumption.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`,
  `Mathlib.AlgebraicGeometry.Scheme`; the structure and its docstring identify a scheme
  with a locally ringed space locally isomorphic to affine spectra.
- `def-weil-irreducible-components`: `irreducibleComponents`,
  `Mathlib.Topology.Irreducible`; its full definition is the set of maximal irreducible
  subsets, exactly the node's Mathlib match. `IsIrreducible` includes nonemptiness.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`,
  `Mathlib.Topology.KrullDimension`; its signature and docstring specify the chain-length
  supremum in `WithBot ℕ∞`.

Edge cases checked by reading the definition and its Mathlib ingredients: empty schemes
impose no conditions; `d = 0` is allowed; a nonempty component of infinite dimension fails
for every finite `d`; components of unequal dimensions fail for each fixed `d`; infinitely
many components are permitted. No assumptions on characteristic, reducedness, a base field,
Noetherianity or quasi-compactness are introduced. Arbitrary scheme universes are allowed.

Searches on 2026-10-15:

- `msearch.py ... leanfinder "scheme pure dimension d every irreducible component has Krull
  dimension d"`: eight hits, including `topologicalKrullDim` and dimension-zero/irreducibility
  facts; none defines pure dimension.
- `msearch.py ... loogle "IsEquidimensional, IsPureDimension, topologicalKrullDim"`:
  zero hits; unknown identifier `IsEquidimensional`.
- `msearch.py ... grep "equidimensional|Equidimensional|PureDimension|pure dimension"`:
  only the unrelated remark about equidimensionality in
  `Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean:65`.
- `msearch.py ... leansearch "scheme equidimensional of pure dimension every irreducible
  component dimension"`: unavailable, Internal Server Error. No search verdict inferred.
- `rg` over upstream `WeilConjectures` and project `lean/Sheaf` for equidimensionality,
  pure dimension and the node id: docstrings and specialized theorems only; no definition.
- `rg` for `IsPureDimension|IsEquidimensional|HasPureDimension` over
  `dag/lean_names_upstream.json`, Mathlib, upstream and project Lean: no matches, including
  no collision for the selected declaration name.

Validation: `scompile.py ND def-weil-pure-dimension` compiled the delivered module cleanly
on the server in 1.1 seconds, nice 19, two threads, 60-second per-file limit.

## Second reading by ND

Independently read the item, all three dependency nodes and their recorded Mathlib
signatures and bodies, the delivered module and node copy, and Stacks topology.tex
Definition 5.10.4 (Tag 0058). The source says simply that every irreducible component
has the same dimension; it assumes only a topological space. Fixing that dimension
and specializing to schemes is exactly the node's stated convention. Also read
Definition 5.10.1 (Tag 0055) for chain length and the dimension range.

Object, hypothesis and conclusion checklist:

- Scheme X: `(X : Scheme.{u})` uses `AlgebraicGeometry.Scheme` from def-pc-scheme.
  Read Scheme.lean:42: a locally ringed space with locally affine neighbourhoods.
  Its carrier coercion gives the underlying topological space. Verdict: exact.
- Nonnegative integer d: `(d : ℕ)` represents precisely the stated nonnegative
  integers, without any positive-dimension assumption. Verdict: exact.
- Pure dimension is a condition, not additional data: `def Scheme.IsPureDimension
  ... : Prop :=` gives the required predicate. Verdict: exact.
- Every irreducible component Z: `∀ Z : Set X, Z ∈ irreducibleComponents X →`.
  Read Irreducible.lean:52 and :107: components are maximal IsIrreducible subsets,
  and IsIrreducible includes nonemptiness, as def-weil-irreducible-components requires.
  No finiteness restriction or component choice is introduced. Verdict: exact.
- Each Z has dimension d: `topologicalKrullDim Z = (d : WithBot ℕ∞)`.
  Read KrullDimension.lean:39, Order/KrullDimension.lean:78, and
  Topology/Sets/Closeds.lean:393: the dimension is the supremum of lengths of strict
  chains of nonempty irreducible closed subsets. This uses the exact declaration
  of def-kun-topological-krull-dimension. Verdict: exact.
- Subspace topology: Z is coerced from a subset to its subtype, with the induced
  topology, so closed subsets in these chains are closed in Z. Verdict: exact.
- Empty scheme: it has no nonempty irreducible subset and therefore no component;
  the universal condition holds for every d. No Nonempty instance is required.
  Verdict: exact; no separate theorem is needed at this definition stage.

Edge cases: d = 0 remains available; infinite-dimensional components cannot equal a
finite natural d; different component dimensions cannot both equal d; any number of
components is permitted, including zero or infinitely many. Nilpotents and the zero
ring's empty spectrum cause no exception because only the underlying topology is
used. No characteristic, base field, Noetherianity, reducedness, quasi-compactness,
or separatedness hypothesis is present or needed. Universe u is explicitly bound;
the subtype of a component lives in that same universe. There are no unbound variables.

Independent searches (2026-10-15), using different phrases from the worker:

- leanfinder: `all maximal irreducible closed subsets of a scheme have identical
  finite dimension` returned eight results about quasi-sobriety, integral schemes,
  locally Artinian schemes and heights; none defines this predicate.
- loogle: `irreducibleComponents, topologicalKrullDim` returned zero hits.
- grep: `equidim|pure.?dim|homogeneous.?dim` over Mathlib returned only the comment
  in AlgebraicCycle/Basic.lean:65.
- leansearch: `topological space all irreducible components have the same Krull
  dimension` was unavailable (HTTP 521); no absence verdict is inferred from it.
- Independently ran rg for those alternatives and the node id over upstream
  WeilConjectures, project lean/Sheaf, and dag/lean_names_upstream.json. Hits are
  docstrings and specialized statements, not an existing definition. Opened project
  Dimension.lean: IsOfRelativeDimension concerns finite-type morphisms and whole
  fibre dimensions, so is a different notion. Opened EquidimensionalOpenLocalDimension
  and ConstantLocalDimensionComponents: these use the component condition inline
  and state consequences under extra assumptions; neither defines it.

H3-H9 review: no semantic mismatch found; no Lean or node changes made. The only
change of this second reading is this review section (plus independent search logs).
There are no new nodes, dependency modules or statement corrections to audit, no
private copies, no hollow data, no theorems or sorries. Imports supply exactly the
three used dependency notions. Module and definition docstrings give the source and
blueprint id. The proof list is empty because this is a definition node. All lines
of the Lean module are within 100 characters. The recorded lean.statement is verbatim
`def Scheme.IsPureDimension (X : Scheme.{u}) (d : ℕ) : Prop`, as in the file.
