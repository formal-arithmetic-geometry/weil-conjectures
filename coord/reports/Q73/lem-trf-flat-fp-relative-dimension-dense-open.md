## Worker report

The item is stated by
`AlgebraicGeometry.flat_finitePresentation_relativeDimension_denseOpen` in
`Sheaf.TraceFormula.FlatFpRelativeDimensionDenseOpen`.  The theorem has one
postponed proof (`sorry`), as required for stage 2.  No definition, new node,
dependency repair, or statement correction was needed.

The Lean module is
`lean/Sheaf/TraceFormula/FlatFpRelativeDimensionDenseOpen.lean`.  It imports
the recorded Mathlib declarations for flatness, locally finite presentation,
open immersions, fibre products, scheme-theoretic fibres, and the existing
`topologicalKrullDimAt`; it also imports the recorded proof-dependency modules
`Sheaf.AlgebraicGeometry.DimensionExtension`,
`Sheaf.AlgebraicGeometry.FlatFibreDimensionStrataCore`, and
`WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso` for the eventual
stage-3 proof.

The node's hypotheses and conclusion render as follows.

- A morphism of schemes `f : X ⟶ S` is the binder
  `{X S U : Scheme.{u}} (f : X ⟶ S)`.
- Flatness and local finite presentation are the typeclass hypotheses
  `[Flat f]` and `[LocallyOfFinitePresentation f]`.
- The open subscheme is represented by `j : U ⟶ S` with
  `[IsOpenImmersion j]`.
- The assertion that the underlying image of `U` is dense, explicitly meaning
  that every nonempty open of `S` meets it, is rendered by
  `hdense : Dense (Set.range j.base)`.  For an open immersion, `Set.range
  j.base` is exactly the underlying open subset.
- The nonnegative integer bound is `(e : ℕ)`; this is the natural-number
  presentation of the node's integer `e ≥ 0`, and Lean coerces it to
  `WithBot ℕ∞` in the dimension inequalities.
- The base change `X_U = X ×_S U` is the actual categorical pullback
  `pullback (C := Scheme.{u}) f j`, and its projection `f_U` is the canonical
  `pullback.snd f j`.
- The hypothesis for every point of `X_U` is
  `hbound : ∀ x : pullback (C := Scheme.{u}) f j,
  topologicalKrullDimAt ((pullback.snd f j).asFiber x) ≤ e`.
  Here `.asFiber x` is the distinguished point in the scheme-theoretic fibre
  over the image of `x`, so this is exactly
  `dim_x((X_U)_{f_U(x)}) ≤ e`.
- The conclusion for every `x : X` is
  `topologicalKrullDimAt (f.asFiber x) ≤ e`, exactly
  `dim_x(X_{f(x)}) ≤ e`.

Dependency declarations read and used:

- `def-weil-flat-morphism`: Mathlib `AlgebraicGeometry.Flat` in
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
- `def-sbc-locally-finite-presentation`: Mathlib
  `AlgebraicGeometry.LocallyOfFinitePresentation` in
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `def-weil-open-immersion`: Mathlib
  `AlgebraicGeometry.IsOpenImmersion` in
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `def-pc-fibre-product`: Mathlib categorical `pullback` and its `fst`/`snd`
  projections in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  with the scheme pullback instance.
- `def-pc-scheme-fibre`: Mathlib `AlgebraicGeometry.Scheme.Hom.fiber` and
  `fiberι` in `Mathlib.AlgebraicGeometry.Fiber`; the point notation `.asFiber`
  is the corresponding recorded Mathlib construction.
- `def-kun-topological-dimension-at-point`: the existing
  `topologicalKrullDimAt` in `WeilConjectures.Mathlib.Topology.KrullDimension`.

The proof-only declarations were also read from their recorded modules:
`AlgebraicGeometry.topologicalKrullDim_fieldExtension_and_denseOpen` in
`Sheaf.AlgebraicGeometry.DimensionExtension`,
`AlgebraicGeometry.exists_fibre_dimension_opens_of_flat_restrict` in
`Sheaf.AlgebraicGeometry.FlatFibreDimensionStrataCore`,
`AlgebraicGeometry.exists_affineChart_baseChangeIso` in
`WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso`,
`IsOpen.topologicalKrullDimAt_eq` and
`topologicalKrullDim_le_of_iSup_eq_top` in
`WeilConjectures.Mathlib.Topology.KrullDimension`, and the Mathlib leaves
`AlgebraicGeometry.UniversallyOpen.of_flat` and
`AlgebraicGeometry.LocallyOfFinitePresentation`.  Their statements support
the seven-step split already recorded in the merged stage-1 node; no proof
fact was added to the theorem statement.

Edge cases checked before drafting: `e = 0`; `U = S`; empty `U` (density then
forces `S` empty); empty `S` and empty `X` (the conclusion is vacuous when
there are no points); empty fibres; non-equidimensional fibres; and a constant
family such as affine space over `S`, where the bound is tested on every
point.  No Noetherian, quasi-compact, separated, reduced, or characteristic
hypothesis was added.

Searches for an existing exact declaration:

- `msearch.py ... leanfinder "flat locally finitely presented morphism relative
  fibre dimension bounded on dense open"`: eight hits, including
  `UniversallyOpen.of_flat`, generic flatness, and smooth-relative-dimension
  declarations; no dense-open fibre-dimension theorem.
- `msearch.py ... loogle "AlgebraicGeometry.Flat,
  AlgebraicGeometry.LocallyOfFinitePresentation, topologicalKrullDimAt"`: zero
  hits; the service reports `topologicalKrullDimAt` as unknown.
- `msearch.py ... grep "relative.*dimension|dimension.*fiber|Dense.*fibre"
  AlgebraicGeometry`: hits only Mathlib smooth/étale relative-dimension text,
  not this theorem.
- `rg` over the upstream `WeilConjectures/` and the project `lean/Sheaf/` for
  the theorem name and the node id: no matching declaration (nearby fibre
  dimension declarations are distinct).  A DAG search found only this item
  and its parent `lem-trf-proper-flat-finite-dense-open`.

No `STATEMENT-DISPUTED` issue or node fault was found.  The file compiles
cleanly through the prescribed `scompile.py` wrapper, with explicit universes,
`autoImplicit false`, no warnings, and only the expected postponed theorem
proof.

## Second reading by Q73

I reread the merged node, its complete statement and proof split, every
recorded statement dependency, and the new theorem signature.  The morphism,
flatness, local finite-presentation, open-immersion, density, nonnegative
dimension bound, pullback fibre, and pointwise conclusion all occur exactly
once.  The pullback projection is `pullback.snd f j`, and the two dimensions
use the canonical `.asFiber` points, so the source's `X_U` and `X` fibres are
rendered without an arbitrary map or an extra hypothesis.  The natural-number
binder retains precisely the source's `e ≥ 0` range.  The statement is
unchanged from the merged DAG node and requires no new node or repair.
