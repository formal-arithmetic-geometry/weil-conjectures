## Worker report

The new module `Sheaf.AlgebraicGeometry.FieldExtensionComponentLocalDimension` states
`AlgebraicGeometry.field_extension_component_local_dimension`, with its entire proof
postponed by `sorry`. It introduces no definitions, extra assumptions, or helper lemmas.
The existing statement and dependency lists are unchanged. No node faults or disputed
statements were found.

Hypotheses and objects, matched against the node:

- `k L : Type u`, `[Field k]`, `[Field L]`, `[Algebra k L]` give precisely a field and an
  arbitrary field extension. The extension morphism is
  `Spec.map (CommRingCat.ofHom (algebraMap k L))`. Both fields and the scheme live in
  the same arbitrary ambient universe, as required by the category of schemes in which
  this fibre product is formed; there is no smallness, finiteness, algebraicity,
  separability, or characteristic restriction on the extension.
- `{Y : Scheme.{u}}`, `(g : Y ⟶ Spec (CommRingCat.of k))`, `[LocallyOfFiniteType g]`
  render the given locally finite type structure morphism. In particular there is no
  quasi-compactness, separatedness, purity, or irreducibility assumption.
- The repeated `pullback g (Spec.map (CommRingCat.ofHom (algebraMap k L)))` is exactly
  the specified Y_L. `pullback.fst g (...)` is its canonical projection p; neither an
  arbitrary replacement map nor a chosen alternative model is used.

Conclusion clauses, in order:

- `IsLocallyNoetherian (pullback ...)` asserts local Noetherianity of Y_L.
- The next conjunct quantifies over every `w` of Y_L and asserts
  `topologicalKrullDimAt w = topologicalKrullDimAt (pullback.fst ... w)`.
- The third conjunct quantifies over every subset D of Y_L with
  `D ∈ irreducibleComponents ...`. Its first clause is `∃ z, IsGenericPoint z D`.
  Its second quantifies over every z with `IsGenericPoint z D` and asserts both
  `topologicalKrullDim D = topologicalKrullDimAt z` and
  `topologicalKrullDimAt z = topologicalKrullDimAt (pullback.fst ... z)`.
  `topologicalKrullDim D` uses the subtype's subspace topology.
- The final conjunct quantifies over every `d : ℕ`, assumes
  `∀ y : Y, topologicalKrullDimAt y = (d : WithBot ℕ∞)`, and concludes
  `topologicalKrullDim D = (d : WithBot ℕ∞)` for every irreducible component D of Y_L.
  All numerical comparisons take place in the same extended dimension type.

Dependency declarations read and used:

- `Field` in `Mathlib.Algebra.Field.Defs`: a nontrivial commutative division ring.
- `Algebra` in `Mathlib.Algebra.Algebra.Defs`: the given field extension, via `algebraMap`.
- `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: the node's local finite type condition.
- `CategoryTheory.Limits.pullback`, `.fst`, `.snd` in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, with the scheme pullback
  instance from `Mathlib.AlgebraicGeometry.Pullbacks`.
- `AlgebraicGeometry.IsLocallyNoetherian` in `Mathlib.AlgebraicGeometry.Noetherian`.
- `topologicalKrullDimAt` in `WeilConjectures.Mathlib.Topology.KrullDimension`, exactly
  the infimum of dimensions of open neighbourhoods, NOT the local ring dimension.
- `irreducibleComponents` in `Mathlib.Topology.Irreducible`: maximal nonempty
  irreducible subsets, hence closed.
- `IsGenericPoint` in `Mathlib.Topology.Sober`: `closure {z} = D`.
- `topologicalKrullDim` in `Mathlib.Topology.KrullDimension`: Krull dimension of the
  topological space, with `WithBot ℕ∞` values.

The proof plan is reproduced step by step in the theorem docstring. Stated proof
interfaces are imported: the finite-type base-change instance, Noetherianity theorem,
scheme sobriety, scheme fibres, dimension definitions, and
`AlgebraicGeometry.fibre_dimension_after_base_change` in
`Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`. The last was read in full.
`lem-trf-locally-algebraic-dimension-components` has neither a Lean record nor a Mathlib
match in the current DAG, so there is no recorded proof-only module to import for it;
its role is explicitly retained in the docstring. It is not needed to type this statement.

Sources read: local Stacks `morphisms.tex`, lemma-dimension-fibre-after-base-change
(Tag 02FY (1)), and lemma-finite-type-noetherian (01T6); `varieties.tex`,
lemma-dimension-locally-algebraic, item-dimension-irreducibles-passing-through
(0A21 (5) / 0B1B), including the proof identifying component dimensions on affine opens.
These justify using topological local dimension and allowing arbitrary field extensions.

Edge cases checked before writing:

- Empty Y: its pullback is empty; the point and component quantifiers are vacuous, and
  local Noetherianity still holds. No `Nonempty` instance is required anywhere.
- `d = 0`: the conclusion is dimension zero for every component, not an assertion that
  the empty scheme has dimension zero. Components are nonempty by definition.
- Identity extensions, purely inseparable extensions, and transcendental extensions all
  satisfy the exact same algebra instance binders. No unwanted finite type condition is
  imposed on `Spec L → Spec k`.
- For an affine line at its generic point the local topological dimension is one, while
  the local ring dimension is zero. The formula uses the former, as the node requires.
- Reducible schemes with unequal-dimensional components are admitted. The component
  equality is asserted only at a generic point of that component, where it is the only
  component through the point. The constant-dimension consequence has its own explicit
  hypothesis and does not silently assume it in the preceding clauses.

Searches for an exact existing statement:

- `msearch.py leanfinder`: “The local topological dimension of a scheme locally of finite
  type over a field is invariant under extension of the ground field, and equals the
  dimension of a component at its generic point”. Eight hits: standard smooth relative
  dimension, function fields, algebraic field ranks, localization presentation dimension,
  and rank at stalk. None states this result.
- `msearch.py leansearch`: “Local topological dimension and the dimension at generic
  points of components are preserved by arbitrary extension of the ground field for a
  locally finite type scheme”. Eight hits include locally finite type base change,
  smooth relative dimension base change, finite presentation/etale base change,
  the Artinian dimension-zero criterion, local Noetherianity, and global
  `topologicalKrullDim`. None states the combined conclusion.
- `msearch.py loogle`, query `topologicalKrullDimAt, topologicalKrullDim`: no hits;
  the service reports the upstream-only `topologicalKrullDimAt` as an unknown identifier.
  Its actual upstream definition was located and read directly.
- `msearch.py grep`, query
  `topologicalKrullDimAt|dimension.*baseChange|dimension.*base_change` in
  `AlgebraicGeometry`: four smooth-relative-dimension hits, requiring smoothness.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `topologicalKrullDimAt|field.extension.*dimension|dimension.*field.extension` found
  existing affine tensor-product local dimension, fibre-dimension comparisons,
  equidimensional-open results, and constant-local-dimension component results. Read
  `WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents` and
  `Sheaf.TraceFormula.RelativeDimensionBaseChange`: the former treats the final
  consequence on locally Noetherian opens and the latter pure relative dimension, not
  all the conclusions here. The private field-extension helper in
  `FibreDimensionAfterBaseChange` supplies only the point equality and is private.
- `grep -rn 'lem-trf-field-extension-component-local-dimension' lean/WeilConjectures`
  found no declaration. Name/concept searches for
  `field_extension_component_local_dimension|FieldExtensionComponentLocalDimension|component.*local.*dimension`
  in both source roots and `dag/lean_names_upstream.json` found no name collision.

Validation: the delivered file is compiled separately using the prescribed server
`scompile.py`; the delivery dry run performs preflight and repeats that file check.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
