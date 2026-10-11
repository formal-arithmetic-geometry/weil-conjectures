## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ComponentIntersectionsFinite.lean` states
`AlgebraicGeometry.component_intersections_finite`, with its sole proof `sorry`.
The docstring carries all three DAG proof steps and names their supporting nodes.
No new notions, dependency modules, or statement corrections are needed.

Hypothesis and clause correspondence:

- Scheme Y: `(Y : Scheme.{u})`, using the unrestricted explicit universe `u`.
- Noetherian: `[IsLocallyNoetherian Y] [CompactSpace Y]`. These are precisely locally
  Noetherian and quasi-compact, equivalent to Mathlib's `IsNoetherian Y`.
- Topological dimension at most one: `(h_dim : topologicalKrullDim Y ≤ 1)`; the
  dimension has codomain `WithBot ℕ∞`, including the empty space's dimension ⊥.
- Finite family of irreducible components: `(irreducibleComponents Y).Finite`.
- Two distinct components: `∀ Z₁ ∈ irreducibleComponents Y,
  ∀ Z₂ ∈ irreducibleComponents Y, Z₁ ≠ Z₂ → ...`.
- Finite intersection: `(Z₁ ∩ Z₂).Finite`.
- Every intersection point closed in Y: `∀ y ∈ Z₁ ∩ Z₂, IsClosed ({y} : Set Y)`.
- T is the union over distinct pairs: the local set expression
  `{y | ∃ Z₁ ∈ irreducibleComponents Y, ∃ Z₂ ∈ irreducibleComponents Y,
  Z₁ ≠ Z₂ ∧ y ∈ Z₁ ∩ Z₂}`. This is exactly membership in that union and introduces
  no separate definition or unconstrained parameter.
- T finite and consisting of closed points: `T.Finite ∧
  (∀ y ∈ T, IsClosed ({y} : Set Y))`.
- Unique component away from T: `∀ y : Y, y ∉ T →
  ∃! Z : Set Y, Z ∈ irreducibleComponents Y ∧ y ∈ Z`.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`,
  `Mathlib.AlgebraicGeometry.Scheme` (available through Noetherian).
  The recorded `Scheme.Hom` was also read; no morphisms occur in this statement.
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`,
  `Mathlib.AlgebraicGeometry.Noetherian`. The recorded Mathlib class is usable:
  Mathlib's existing affine-cover characterization identifies the every-affine-open
  presentation with the DAG's existence-of-a-cover presentation.
- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace`,
  `Mathlib.Topology.Defs.Filter` (transitively imported), expressly without Hausdorffness.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`,
  `Mathlib.Topology.KrullDimension`, the supremum of lengths of strict chains of
  nonempty irreducible closed subsets.
- `def-weil-irreducible-components`: `irreducibleComponents`,
  `Mathlib.Topology.Irreducible` (transitively imported), maximal irreducible subsets.

Source: [Stacks Tag 09NX](https://stacks.math.columbia.edu/tag/09NX), Lemma 33.38.10,
proof first paragraph for finite closed T, and final paragraph for uniqueness outside T.
The local literature checkout was absent, so the official Stacks page was opened instead.
The component-intersection argument depends only on Noetherianity and dimension ≤ 1,
not on the reducedness or separatedness used for the lemma's ample-sheaf conclusion.

Edge cases checked: the empty scheme has no components, empty T, and vacuous point
clauses; a dimension-zero Noetherian scheme has disjoint singleton components; an
integral curve has one component and T empty; two lines meeting in one closed point
have singleton T; a disjoint point and curve have T empty. Nonreduced schemes are
included because components and dimension are topological. No field or characteristic
assumption is introduced. Closed points mean singleton closed in Y, not in the
intersection alone. No statement dispute or node fault was found.

Searches (via `/home/ubuntu/weil-launcher/msearch.py` unless specified):

- LeanFinder: `Noetherian scheme dimension at most one distinct irreducible components
  intersection finite closed points`: eight hits, including
  `finite_irreducibleComponents_of_isNoetherian` and dimension-zero Artinian results;
  none states the full conjunction.
- Loogle: `irreducibleComponents, Set.Finite`: five hits, including finite components
  and component-union lemmas; none states finite distinct intersections and closedness.
- Mathlib grep: `irreducibleComponents.*(inter|finite)|finite.*irreducibleComponents`:
  eighteen hits on finiteness, generic points, and applications; no exact statement.
- LeanSearch: `Noetherian dimension one scheme distinct irreducible components finite
  intersection closed points`: service unavailable (Internal Server Error), no results.
- Direct rg in `WeilConjectures/` and `lean/Sheaf/`:
  `component.*inter|inter.*component|lem-sc-component-intersections-finite` found only
  other constructions and statements involving component intersections, no exact theorem.
- Direct rg for `component_intersections_finite` in Mathlib, WeilConjectures,
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found no collision.

Server validation: `scompile.py M1 lem-sc-component-intersections-finite` compiled the
module in 1.6 seconds, exit code 0, no errors or warnings. The only subsequent edit
removed an accidental leading space in a docstring. Delivery dry run follows.

## Second reading by M1

I independently matched the node's clauses with
`AlgebraicGeometry.component_intersections_finite` in
`lean/Sheaf/AlgebraicGeometry/ComponentIntersectionsFinite.lean`.

- The object `Y` is rendered as `(Y : Scheme.{u})`; the node's Noetherian
  hypothesis is rendered by `[IsLocallyNoetherian Y] [CompactSpace Y]`, namely
  locally Noetherian plus quasi-compact, with no separatedness, reducedness,
  field, or characteristic assumption.
- The dimension hypothesis is exactly `(h_dim : topologicalKrullDim Y ≤ 1)`,
  retaining the `WithBot ℕ∞` dimension and the empty-space case.
- The component family is exactly `irreducibleComponents Y`, and its finiteness
  is the first conjunct `(irreducibleComponents Y).Finite`.
- The pairwise clause quantifies both components over that family, assumes
  `Z₁ ≠ Z₂`, and states both `(Z₁ ∩ Z₂).Finite` and
  `∀ y ∈ Z₁ ∩ Z₂, IsClosed ({y} : Set Y)`.
- The local `let T : Set Y := {y | ∃ Z₁ ... ∃ Z₂ ..., Z₁ ≠ Z₂ ∧
  y ∈ Z₁ ∩ Z₂}` is exactly the union over distinct ordered pairs.  The next
  clauses state `T.Finite`, closedness of every singleton in `T`, and
  `∀ y, y ∉ T → ∃! Z, Z ∈ irreducibleComponents Y ∧ y ∈ Z`, preserving the
  node's final uniqueness quantifier.

No mismatch was found and no Lean source change was needed.  I checked edge
cases including the empty scheme (empty components and `T`), dimension zero,
an integral curve (one component), intersecting components, and nonreduced
schemes; all are covered by the unrestricted topological formulation.  Searches
for an existing exact declaration in Mathlib, `WeilConjectures/`, `lean/Sheaf/`,
and `dag/lean_names_upstream.json` found none; LeanFinder and Loogle found only
partial component or Noetherian results, and LeanSearch was unavailable.
The module compiles cleanly with `scompile.py`; its only proof is the required
named theorem `component_intersections_finite` with `sorry`.
