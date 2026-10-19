## Worker report

Record an existing statement, with no new Lean module:
`AlgebraicGeometry.IsCurve.exists_isAffineOpen_dense_finite_compl` in
`WeilConjectures.AlgebraicGeometry.Curve.AffineCore`, branch `slopmaster2`.
The full published module was read using `scompile.py --source`, including its
signature, docstring, and proof. The node's upstream audit names this exact theorem,
with `sorry: false`, and `dag/lean_names_upstream.json` associates it with this node.
The older local upstream checkout lacks AffineCore; the published source resolves it.
No declaration is duplicated. The only changed node field is `lean`.

Source read: the node and both blueprint snapshots' file
`blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/lem-a1-affine-core-of-curve.md`.
The current main-20261015 snapshot has the identical statement (order 3148).
The master's proof was also read. No repair note exists for this item.

Hypothesis-by-hypothesis correspondence:

- The base field is `{k₀ : Type u} [Field k₀]`; no algebraic closure,
  finiteness, perfectness, or characteristic assumption is imposed.
- A scheme over that field is `{C : Scheme.{u}} (p : C ⟶ Spec (.of k₀))`.
  The explicit structure map is the interface of the recorded curve declaration.
- The word curve is `[IsCurve p]`: separated, locally of finite type,
  quasi-compact, and topological Krull dimension at most one. This is the
  `def-sc-curves` recorded declaration, not a private substitute.
- Smoothness and the dimension-one part of geometrically a connected curve are
  expressed by `[SmoothOfRelativeDimension 1 p]`.
- `[GeometricallyConnected p]` says that every field base change is connected,
  including nonempty. Along with smooth relative dimension one, every such
  base change is a nonempty connected one-dimensional curve. Conversely a
  smooth geometrically connected curve of dimension one has relative dimension
  one: smooth connected curves are regular and irreducible, and the upstream
  `smoothOfRelativeDimension_iff_topologicalKrullDim_eq` identifies these dimension
  conditions. Thus the relative-dimension hypothesis adds no restriction to the
  node's phrase "geometrically a connected curve".

Clause-by-clause correspondence:

- An open subscheme is `∃ V : C.Opens`; its scheme is the usual open restriction.
- Affineness is `IsAffineOpen V`.
- Nonemptiness is `(V : Set C).Nonempty`.
- Density is `Dense (V : Set C)`.
- Finite complement is `(V : Set C)ᶜ.Finite`. This complement is closed because
  V is open; density on the one-dimensional irreducible curve excludes the
  generic point. Thus its points are closed, not generic points. Each closed
  point of a finite-type scheme over a field has finite residue field extension.
  The reduced closed complement is consequently a finite disjoint union of
  spectra of finite field extensions, hence finite over the base field.
  Conversely a finite scheme over the field has finitely many points. This
  explains the exact equivalence with "finite over the base field": the node
  specifies an open, and no extra scheme structure on its complement. Even any
  closed-subscheme structure supported on this complement is finite over the
  field, since it is a zero-dimensional finite-type scheme. No rational-point
  or algebraically-closed-field restriction is hidden here.

Dependency interfaces read:

- `def-sc-curves`: `AlgebraicGeometry.IsCurve` in
  `WeilConjectures.AlgebraicGeometry.Curve`. Read the full class signature and
  docstring locally and in the current published source. Also read
  `AlgebraicGeometry.IsConnectedCurve`, which includes nonemptiness and exact
  dimension one. The dependency's main-20261015 update allows any field.
- `def-weil-pbc-scheme-conventions` has `lean.convention: true` and no declaration.
  Its statement explicitly introduces no new notion. Its recorded Mathlib
  conventions apply directly, in particular the affine open notion.
- Read the Mathlib definition/docstring `AlgebraicGeometry.GeometricallyConnected`
  in `Mathlib.AlgebraicGeometry.Geometrically.Connected` and the full signature
  and docstring of `AlgebraicGeometry.smoothOfRelativeDimension_iff_topologicalKrullDim_eq`
  in `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- The proof dependencies' records are the existing upstream
  `AlgebraicGeometry.IsConnectedCurve.exists_smooth_properCompactification` and
  `AlgebraicGeometry.IsConnectedCurve.isAffine_of_ne_top` in
  `WeilConjectures.AlgebraicGeometry.Curve.Compactification`. This delivery
  introduces no module needing proof imports. The existing proved affine-core
  theorem instead chooses any nonempty affine open: regularity and connectedness
  give irreducibility, which gives density, and the Noetherian dimension-one
  complement lemma gives finiteness. Its proof was read in full.

Edge cases checked: the empty scheme fails geometric connectedness. A point
`Spec k₀` fails the dimension-one condition even though it is connected. A
geometrically disconnected curve fails geometric connectedness. A curve of
positive genus and a proper curve are included; the open is then strictly smaller but
nonempty. Already affine curves are included, and an empty complement is allowed.
Closed points need not be rational. Arbitrary fields, including imperfect fields
and finite fields, are included. Universe u is arbitrary; no independent smaller
universe for test fields or schemes is imposed by this statement.

Searches actually run:

- `msearch.py leanfinder`, query "smooth curve geometrically connected nonempty
  dense affine open finite complement": eight Mathlib results including
  `Scheme.IsQuasiAffine`, `IsIntegral`, and `IsDominant`, no exact statement.
- `msearch.py leanfinder`, query "affine open dense finite complement smooth
  geometrically connected curve": eight results including quasi-affineness,
  smooth local presentations, and rational-map density; no exact statement.
- `msearch.py leansearch`, query "smooth geometrically connected curve affine
  open finite complement": eight results including `IsAffineOpen` and affine
  open compactness, no full theorem.
- `msearch.py loogle`, queries
  "exists_isAffineOpen_dense_finite_compl, IsConnectedCurve" and
  "IsCurve.exists_isAffineOpen_dense_finite_compl": unknown identifier, no hits
  (these upstream names are absent from the Mathlib search service).
- `msearch.py grep`, query "isAffineOpen.*dense|dense.*finite_compl" in
  `AlgebraicGeometry`: no Mathlib hits. Searches for the upstream theorem name
  and `IsCurve` with a WeilConjectures subdirectory also returned no hits from
  that Mathlib-scoped tool, so direct upstream inspection was used.
- Direct `rg` searches of the local upstream tree for the full declaration,
  module name, affine-core terms, and node id: no affine-core match in that
  older checkout. Direct `rg` searches of `lean/Sheaf` found related curve
  results, but no duplicate affine-core declaration.
- The node's `lean_audit` and `dag/lean_names_upstream.json` identified the exact
  upstream match. `scompile.py --source` retrieved the entire current published
  AffineCore module, which confirms the match and its explicit proof.

No statement correction, new node, dependency repair, or disputed statement.
The existing-declaration compile probe and server preflight are run by deliver2.py.

## Second reading by Q144

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
