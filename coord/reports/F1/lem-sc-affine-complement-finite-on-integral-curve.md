## Worker report

The module `Sheaf.AlgebraicGeometry.AffineComplementFiniteOnIntegralCurve` states
`AlgebraicGeometry.IsAffineOpen.finite_compl_of_integral_dim_one`, with its sole proof
`sorry`. There are no definitions or additional declarations.

Source read: Stacks Project, Varieties, Tag 09ND,
`lemma-dim-1-noetherian-integral-separated-has-ample`, second proof sentence,
“Since X is Noetherian, each of the sets X minus U_i is finite.” The local repository's
literature checkout is absent; the same source was read at
`/home/ubuntu/c1-stacks-review/varieties.tex`, lines 7926–7946. The node isolates the
finite-complement assertion, which does not require the separatedness needed later
for ampleness. Its existing reviewed proof explains this generalization.

Hypothesis and conclusion correspondence:

- Scheme X: `{X : Scheme.{u}}`, for an arbitrary explicitly bound universe u.
- Integral: `[IsIntegral X]`, including nonemptiness, reducedness and irreducibility.
- Noetherian: `[IsLocallyNoetherian X] [CompactSpace X]`, exactly locally Noetherian
  plus quasi-compact, using the two dependency notions explicitly.
- Topological Krull dimension exactly one: `hdim : topologicalKrullDim X = 1`.
- Every open subscheme: arbitrary `{U : X.Opens}`, the underlying open with its
  canonical restricted scheme structure.
- Affine: `hU : IsAffineOpen U`, which Mathlib defines as `IsAffine U`.
- Nonempty: `hne : (U : Set X).Nonempty`.
- Finite complement as a set of points: `((U : Set X)ᶜ).Finite`.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` in
  `Mathlib.AlgebraicGeometry.Scheme`, lines 36–47; open subschemes and affine opens
  are rendered using `Scheme.Opens` and `AlgebraicGeometry.IsAffineOpen`, the latter
  read in `Mathlib.AlgebraicGeometry.AffineScheme`, lines 250–252.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral` in
  `Mathlib.AlgebraicGeometry.Properties`, lines 238–243, with its full fields read.
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian` in
  `Mathlib.AlgebraicGeometry.Noetherian`, lines 56–59.
- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace` in
  `Mathlib.Topology.Defs.Filter`, lines 280–285 (no separation condition).
- `def-kun-topological-krull-dimension`: `topologicalKrullDim` in
  `Mathlib.Topology.KrullDimension`, lines 35–40, valued in `WithBot ℕ∞`.

The first three dependencies are available through the Noetherian and Properties
imports; the dimension import supplies the dimension notion. No dependency modules
or new nodes are needed. All variables and the universe are bound explicitly.
The declaration docstring reproduces all three node proof steps and names their
supporting nodes, including sobriety for the T0 hypothesis.

Edge cases checked: U = X gives an empty, finite complement whenever X itself is
affine; a usual affine chart in the projective line has a singleton complement;
Spec of a DVR with the generic-point affine open has a singleton complement.
Empty U is excluded by the node and by hne. Empty X is excluded by integrality and
also has dimension bottom, not one. Dimension zero and dimensions above one are
excluded by the exact dimension equation. No field, characteristic, properness,
separatedness or finite-type hypothesis is imposed. No statement fault or dispute found.

Searches actually run with `/home/ubuntu/weil-launcher/msearch.py`:

- LeanFinder: `Every nonempty affine open subset of a Noetherian integral scheme of
  dimension one has finite complement`: eight hits, including Noetherian affine
  open and finite irreducible-component facts, but no exact statement.
- Loogle: `IsOpen.finite_compl_of_topologicalKrullDim_le_one`: unknown identifier,
  zero hits (this declaration is upstream project code, not Mathlib).
- LeanSearch: `nonempty affine open integral Noetherian curve finite complement`:
  service unavailable, Internal Server Error; no mathematical verdict inferred.
- Mathlib grep: `finite_compl|compl_finite` in `Topology`: three unrelated hits
  (Irreducible, OnePoint, DiscreteSubset), no matching declaration.

Direct source searches: `rg` for `finite.*compl|compl.*finite|affine.*complement` in
WeilConjectures and lean/Sheaf found the upstream generic topological theorem
`IsOpen.finite_compl_of_topologicalKrullDim_le_one` and specialized curve applications.
Its full signature/docstring were read in
`WeilConjectures/Mathlib/Topology/KrullDimension.lean`, lines 104–110. It concerns
irreducible quasi-sober Noetherian T0 spaces of dimension at most one and arbitrary
nonempty opens; it is not the exact scheme statement with dimension exactly one
and affine open hypothesis of this node. `IsCurve.exists_isAffineOpen_finite_compl`
is likewise existential and assumes a curve over a field. Neither is an exact
existing declaration for this node. Searches for the item id in WeilConjectures
returned no hits. A narrower search for `IsAffineOpen.*finite|finite.*IsAffineOpen|
finite_compl` in lean/Sheaf/AlgebraicGeometry found no exact statement. Searches of
Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for the chosen
new declaration name found no collisions.

Server compile: scompile.py compiled the 42-line module successfully (exit code 0,
1.6 seconds), with no warnings or errors. The delivery dry run is the final check;
the independent second reading is left to the designated second reader.

## Second reading by F1

I independently read the node, its Stacks source place (Varieties Lemma 09ND,
proof sentence “Since X is Noetherian, each of the sets X \\setminus U_i is finite”),
and the Lean declaration. The statement list and verdicts are:

- The object `X` is an arbitrary scheme `Scheme.{u}`; Lean binds `{X : Scheme.{u}}`.
  Verdict: exact, with the universe explicit.
- `X` is integral; Lean has the instance `[IsIntegral X]`. Verdict: exact use of
  `def-pc-integral-scheme`.
- `X` is Noetherian; Lean renders this as
  `[IsLocallyNoetherian X] [CompactSpace X]`, the project's locally Noetherian plus
  quasi-compact convention. Verdict: exact, with no separation or finite-type
  assumption added.
- `X` has topological Krull dimension one; Lean has
  `(hdim : topologicalKrullDim X = 1)`. Verdict: exact (the numeral is in the
  codomain of `topologicalKrullDim`).
- `U` is an open subscheme of `X`; Lean binds `{U : X.Opens}` and uses its
  underlying set `(U : Set X)`. Verdict: exact.
- `U` is affine; Lean has `(hU : IsAffineOpen U)`. Verdict: exact Mathlib
  `IsAffineOpen`; retaining this hypothesis matches the node even though the
  generic topological finiteness theorem can prove the result without using it.
- `U` is nonempty; Lean has `(hne : (U : Set X).Nonempty)`. Verdict: exact.
- The conclusion that `X \\setminus U` is a finite set of points is rendered as
  `((U : Set X)ᶜ).Finite`. Verdict: exact set complement and finiteness predicate.

No mismatch was found and no statement or dependency record was changed. The
Lean docstring carries the node's three proof steps, including the sobriety/T0
argument and the closed-points finiteness step.

Edge cases were checked independently: `U = X` gives the empty finite complement;
`U = ∅` is excluded by `hne`; an affine chart in `ProjectiveLine` has a singleton
complement; a generic-point affine open in a DVR has the closed point as complement;
empty `X` is ruled out by integrality (and cannot have dimension one); dimensions
zero or greater than one fail `hdim`; no field, characteristic, properness,
separatedness, or finite-type hypothesis is present. Universes are explicit and
there are no index sets or zero-object cases.

Searches for an existing declaration were repeated with `rg` over Mathlib,
`WeilConjectures`, and `lean/Sheaf`, and with `msearch.py` LeanFinder/Loogle/
LeanSearch queries for “finite complement affine open integral curve”. They found
only the generic `IsOpen.finite_compl_of_topologicalKrullDim_le_one` and the
existential `IsCurve.exists_isAffineOpen_finite_compl`; neither has this node's
scheme-level statement. No declaration-name collision was found. The module
compiled cleanly with `scompile.py`; no repair was necessary.
