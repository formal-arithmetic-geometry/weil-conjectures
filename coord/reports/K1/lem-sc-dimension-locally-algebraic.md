## Worker report

The module `Sheaf.AlgebraicGeometry.DimensionLocallyAlgebraic` states
`AlgebraicGeometry.dimension_locally_algebraic` with a single `sorry`; it defines no new
notion and proves nothing. Its docstring carries all six steps of the node's proof and names
their dependency nodes.

Source checked: https://stacks.math.columbia.edu/tag/0A21, Lemma 33.20.3 (3), including its
proof. The local `literature/stacks-project/varieties.tex` is absent on this machine, so the
published Stacks page was read. It asserts precisely both clauses of the node. No statement
correction, disputed statement, or dependency fault was found.

Hypotheses and conclusions, clause by clause:

- A field k: `{k : Type u} [Field k]`.
- A scheme X over k: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`. The arrow
  `X ↘ Spec (.of k)` is its structure morphism.
- Locally of finite type: `[LocallyOfFiniteType (X ↘ Spec (.of k))]`.
- Irreducible X: `[IrreducibleSpace X]`, including nonemptiness, with no reducedness assumption.
- Every nonempty open subset U: `∀ U : X.Opens, (U : Set X).Nonempty →`.
  `X.Opens` is the type of all open subsets, with their subtype topology.
- The first equality: `topologicalKrullDim (U : Set X) = topologicalKrullDim X`.
- Every point x: `∀ x : X`.
- The second equality: `topologicalKrullDimAt x = topologicalKrullDim X`.
- Both conclusions are required together by `∧`.

Dependency declarations read and used:

- `def-weil-irreducible-components`: `Mathlib.Topology.Irreducible`,
  `irreducibleComponents` and the same module's `IsIrreducible`/`IrreducibleSpace`.
  The node includes irreducibility of a space; `IrreducibleSpace` expresses exactly that
  part, as `irreducibleSpace_def` shows. No components are needed in the statement.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`. Its full all-affine-pairs signature and docstring
  were read. Only local finite type is assumed; quasi-compactness is not assumed.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`, the Krull dimension of `IrreducibleCloseds` with values in
  `WithBot ℕ∞`. Imported through the recorded local-dimension module below.
- `def-kun-dimension`: `WeilConjectures.Mathlib.Topology.KrullDimension`,
  `topologicalKrullDimAt`. Its full definition is the infimum over all open neighbourhoods,
  agreeing with the minimum in the node because this nonempty set of values lies in the
  well-ordered dimension range. This is dimension at a point, not stalk ring dimension.

Edge cases checked: the empty scheme is excluded by irreducibility's nonemptiness, as in the
node; empty U is excluded only from the first conclusion by its stated hypothesis. U = X
is included. Zero-dimensional schemes, generic points, closed points, positive-dimensional
schemes and nonreduced irreducible schemes are all included. No affine, separated, reduced,
quasi-compact, smooth, characteristic, or dimension bound has been added. The universes are
explicit: the field and scheme live at arbitrary `u`, following the project's scheme-over-field
convention and the source declarations; no universe or variable is auto-bound.

Searches made (the remote search results are also in `searches.jsonl`):

- msearch leansearch: "Every nonempty open subset of an irreducible scheme locally of finite
  type over a field has the same Krull dimension and dimension at every point".
  Service unavailable (Internal Server Error); no claim of a negative result from this service.
- msearch leanfinder: "Every nonempty open subset of an irreducible locally algebraic scheme
  has the same Krull dimension and every point has that dimension". Eight hits: the dimension
  definition, quasi-sobriety, integral/irreducible relationships and closed-point height;
  none asserts this statement.
- msearch loogle: `topologicalKrullDim, AlgebraicGeometry.LocallyOfFiniteType`.
  Zero hits.
- msearch grep of Mathlib: `topologicalKrullDim.*(opens|irreducible)|topologicalKrullDimAt`.
  Zero hits.
- rg of WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json:
  `topologicalKrullDim_opens_eq|topologicalKrullDimAt|dimension_locally_algebraic`.
  Found `AlgebraicGeometry.topologicalKrullDim_opens_eq` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, whose full signature and
  docstring were read: it assumes `IsIntegral X` and states only the open-subset equality.
  It therefore does not replace this irreducible (possibly nonreduced) two-clause statement.
  Other hits concern smooth relative dimension or the general local-dimension definition.
- rg of WeilConjectures for `lem-sc-dimension-locally-algebraic`: no hits.
- rg of Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  `dimension_locally_algebraic`: no hits; the chosen declaration name is new.

Validation: `scompile.py K1 lem-sc-dimension-locally-algebraic` compiled the 57-line module
on the server in 1.7 seconds, exit code 0, no warnings. The declaration binds every variable
and universe explicitly and its only proof is `by sorry`.

## Second reading by K1

I reread the node `lem-sc-dimension-locally-algebraic`, its source (Stacks Tag 0A21,
Lemma 33.20.3, part (3)), the dependency node signatures, and
`Sheaf.AlgebraicGeometry.DimensionLocallyAlgebraic`. The item list and verdicts are:

- The field `k` is rendered by `{k : Type u} [Field k]`; this has the same arbitrary
  characteristic and universe as the node.
- The scheme over `k` is rendered by `(X : Scheme.{u}) [X.Over (Spec (.of k))]`, with
  structure map `X ↘ Spec (.of k)`.
- Local algebraicity (locally finite type) is exactly
  `[LocallyOfFiniteType (X ↘ Spec (.of k))]`; no quasi-compactness or finite type
  hypothesis is added.
- Irreducibility is exactly `[IrreducibleSpace X]`, including nonemptiness and without
  a reducedness, separatedness, or affine assumption.
- For each `U : X.Opens` with `(U : Set X).Nonempty`, the first conclusion is exactly
  `topologicalKrullDim (U : Set X) = topologicalKrullDim X`.
- For each `x : X`, the second conclusion is exactly
  `topologicalKrullDimAt x = topologicalKrullDim X`.
- The conjunction `∧` requires both clauses, with the same quantifier order as the node.

The declarations used are the recorded `LocallyOfFiniteType`, Mathlib's
`topologicalKrullDim`, and the project's `topologicalKrullDimAt`; each matches the
corresponding dependency notion. The source's reduction-to-integral argument and its
six proof steps are preserved in the theorem docstring, while the theorem proof remains
only `by sorry` as required. The empty scheme is excluded by irreducibility, empty opens
are excluded only by the explicit nonempty premise, `U = X` is included, and zero-,
positive-dimensional, generic-point, closed-point, and nonreduced irreducible cases are
covered. No mismatch was found and no file or node statement required repair. Searches
reported no existing declaration with this exact two-clause statement; the existing
integral-only open-dimension theorem is insufficient.
