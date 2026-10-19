## Worker report

The module `Sheaf.TraceFormula.FlatFiniteTypeDensePresentation` states the Tag 081N
relative flatness extension lemma with theorem declaration
`AlgebraicGeometry.flat_finite_type_dense_presentation`. Its proof is `sorry`, as required
for stage 2; no definition data is introduced.

The binders render the node statement clause by clause. `X` and `S` are schemes in one
universe (`{X S : Scheme.{u}}`), and `f : X ⟶ S` is locally of finite presentation through
the typeclass `[LocallyOfFinitePresentation f]`. The module is `F : X.Modules`; the
finite-type quasi-coherent hypothesis is
`hF : Scheme.Modules.IsQuasiCoherentFiniteType F`, which is the recorded dependency
notion. Relative flatness over `S` is
`hflat : Scheme.Modules.IsFlatOver F f`, using the recorded affine-local definition.
The base open is `U : S.Opens`. Its retrocompactness is rendered by
`hUretro : IsRetrocompact (U : Set S)`, whose Mathlib definition says that intersection
with each quasi-compact open is quasi-compact. Its scheme-theoretic density is rendered
by `hUdense : SchematicallyDenseOpen U`, the existing project declaration for injectivity
of every structure-sheaf restriction to `W ∩ U`, equivalent to injectivity of
`𝒪_S → j_*𝒪_U`. Finally, restriction of `F` to `f ⁻¹ᵁ U` is
`(Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F`; the hypothesis
`hUfp : (...).IsFinitePresentation` states finite presentation there, and the conclusion
`F.IsFinitePresentation` states finite presentation on all of `X`.

The module imports `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` for
`LocallyOfFinitePresentation`, `Mathlib.AlgebraicGeometry.Restrict` for opens, preimages,
and module restriction, `Sheaf.AlgebraicGeometry.CoherentFiniteType` for the recorded
finite-type quasi-coherent notion, `Sheaf.TraceFormula.SchematicallyDenseOpen` for its
recorded schematic-density declaration, and
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic` for `IsFlatOver`.
The proof-plan dependencies are reflected in the docstring: affine reduction; finite
principal covering from retrocompactness and the product-localization injection from
schematic density; the Tag 05I7 stalk finite-presentation input
`lem-trf-flat-finite-type-flat-point-local`; Tag 00RC openness of flatness
`lem-weil-pbc-openness-of-flatness`; the localization comparison; and local gluing of
finite presentation.

Edge cases checked against the statement are `U = ⊤` (retrocompact and density are
immediate, so the restriction hypothesis is the original one), `U = ⊥` (schematic density
forces the base to have zero structure sheaf, so no hidden non-dense empty-open case is
introduced), the empty source scheme, and `F = 0` (all finite-type, flatness, and finite
presentation clauses remain meaningful, with the restriction still zero).

Searches made before writing:

- `msearch.py NP lem-trf-flat-finite-type-dense-presentation leanfinder "A finite type
  quasi coherent module flat over a locally finitely presented scheme morphism is finitely
  presented if finitely presented over a retrocompact schematically dense open"`: 8 hits,
  all general finite-presentation or locally-finite-presentation declarations; no exact
  combined theorem.
- `msearch.py NP lem-trf-flat-finite-type-dense-presentation loogle
  "SchematicallyDenseOpen, IsRetrocompact, IsFlatOver, IsFinitePresentation"`: 0 hits
  (the search service reported unknown identifier `SchematicallyDenseOpen`).
- `msearch.py NP lem-trf-flat-finite-type-dense-presentation grep
  "schematicallyDense|schematically.dense"`: 0 hits in its Mathlib search scope; a direct
  `rg` over the project found the existing `Sheaf.TraceFormula.SchematicallyDenseOpen`
  declaration, which is reused.
- `rg` over `WeilConjectures/` and `lean/Sheaf/` for the item id and the key predicates:
  no existing item theorem; the existing finite-type, flat-over, restriction, and
  schematic-density declarations were inspected in full.

The file compiled cleanly with `scompile.py`; the only accepted diagnostic is the theorem's
use of `sorry`.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
