## Worker report

The module `Sheaf.AlgebraicTopology.CoherentRealizationRelativeCells` states
`SSet.coherent_realization_relative_cells`.  It uses the recorded declarations
`SSet.PinchedCube.rigidification` from
`Sheaf.AlgebraicTopology.PinchedCubeLatching`, `SSet.Bergner.U`,
`SSet.Bergner.emptyCat`, `SSet.Bergner.oneCat`, `SSet.Bergner.fromEmpty`, and
`SSet.Bergner.bundleMap` from `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`.
The sequence colimit is `Functor.ofSequence` and `Cocone`/`IsColimit` from
Mathlib.

`relativeCellSource`, `relativeCellTarget`, and `relativeCellMap` render the two
allowed generators: `emptyCat ⟶ oneCat` and
`bundle (U (boundary r)) ⟶ bundle (U (Delta r))`.  `RelativeCellStep` renders a
small coproduct of these maps, its pushout square, and the requirement that the
standard top `r`-simplex of every mapping cell is not in the old stage (using
`HEq` so the endpoint objects may coincide).  `HasRelativeCellPresentation`
then renders, clause by clause, the degreewise-injective coherent-realization
map, `D₀ = C[X]`, injective stage inclusions into `C[Y]`, injective transition
maps, compatibility with the ambient map, a countable sequence colimit, and
when the vertex map is bijective a fixed-object sequence with no object cells
and identity object maps.

For the node statement's hypotheses and clauses, the Lean rendering is:

* The small simplicial sets and degreewise-injective map are `X Y : SSet.{u}`,
  `i : X ⟶ Y`, and `hinj : ∀ d, Function.Injective (i.app d)`.
* `D₀ = C[X]` is the equality field `D0`; `C[Y]` is
  `SSet.PinchedCube.rigidification.obj Y`; the source map is
  `SSet.PinchedCube.rigidification.map i`.
* Stage inclusions and transition inclusions are the object and every mapping
  simplicial-set injectivity clauses on `inc` and `step`.
* The countable presentation is `Functor.ofSequence step`, a `Cocone`,
  `Nonempty (IsColimit c)`, and an isomorphism to `C[Y]` commuting with every
  stage inclusion.
* Each transition is the `RelativeCellStep` pushout of the displayed small
  coproduct, with `r : I₁ → ℕ` and `I₀` indexing object cells.
* The top-simplex clause uses
  `SSet.stdSimplex.objMk (OrderHom.id : Fin (r k + 1) →o Fin (r k + 1))`
  and excludes all old-stage images by `HEq`.
* The vertex-bijective case quantifies over a fixed object type `O`, fixed
  enrichments `F j : Bergner.Fixed O`, fixed-object maps, an ambient fixed
  enrichment `E`, and requires injective fixed-stage and fixed-transition mapping maps, `IsEmpty s.I₀`
for every transition cell step, and identity object maps.

Edge cases checked before writing: `r = 0` makes `boundary 0` empty and the
standard top is still well-typed; `X = Y` permits the identity inclusion and an
empty family of mapping cells; empty simplicial sets are allowed; coincident
cell endpoints are allowed by the `HEq` top condition; no Kan or finiteness
hypothesis occurs.  The fixed-object clause uses `Bergner.Fixed`, whose map
object function is definitionally `id`.

Searches made: `msearch.py NE lem-coef-coherent-realization-relative-cells
leanfinder "The coherent realization of a simplicial subset is a relative
simplicial computad built by attaching boundary simplices in hom objects"`
(no exact match); `msearch.py ... loogle "SimplicialThickening"` (only the
ordinary subset-poset thickening); `msearch.py ... grep
"computad|coherentRealization|coherent.realisation|homotopy.coherent|SimplicialThickening"`
(Mathlib hits only `SimplicialNerve.lean`); and analogous LeanFinder searches
for simplicial-computad relative presentations (only generic simplicial-set
cofibration generators).  `rg` over `WeilConjectures` and the project
`lean/Sheaf` found no exact declaration.  The existing `CoherentFixedVertexCofibrations`
and `CoherentNerveCellFiltration` statements concern fixed-vertex cofibrations
or inner horns and do not state this arbitrary degreewise-injective relative
cell presentation.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
