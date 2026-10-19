## Worker report

`Sheaf.AlgebraicTopology.MappingPathSquareRectification` states
`SSet.Enhanced.mapping_path_square_rectification`, with its entire proof `sorry`.
It retains the saved packet's mapping-path and homotopy-fiber models and repairs
its quantifiers, coherence witnesses, relative uniqueness, and missing realization
clause. The mathematical node statement is unchanged. No new mathematical
hypothesis is imposed, and no theorem other than this node is postponed.

The following matches every hypothesis and clause of the node to the Lean:

- Small simplicial sets and the four Kan complexes are `{X Y S T : SSet.{u}}`
  and the four explicit `KanComplex` instances. The universe `u` is explicit.
- The maps are `(r : X ⟶ S) (q : Y ⟶ T) (u : X ⟶ Y) (v : S ⟶ T)`.
  The specified homotopy from `qu` to `vr` is
  `H : SSet.Homotopy (u ≫ q) (r ≫ v)`, with `H.h : X ⊗ Δ[1] ⟶ T`.
- `mappingPath r` and `mappingPath q` are the existing degreewise initial-endpoint
  pullbacks, rather than chosen equivalent replacements. `mappingPathSource`
  is `e_r` or `e_q`; the existing `mappingPathProjection` is `R` or `Q`.
  `mappingPathPath` is the second coordinate of the same subcomplex inclusion.
- The horn map is the existential `h`. `mappingPathHornMap H h` identifies its
  restriction along `horn₂₁.ι₀₁` with `H(e_r,-)` and along `horn₂₁.ι₁₂` with
  `mappingPathPathMap r v`. The latter is evaluation of the universal path after
  postcomposition by `v`; braiding corrects the internal-hom argument order.
- Existence of an extension is the separate existential `∃ C, ... ≫ C = h`.
  Its consequences hold for **every** extension, through
  `∀ C, (𝟙 _ ⊗ₘ (SSet.horn 2 1).ι) ≫ C = h → ...`.
- `mappingPathInducedBy r q u v C U` states the two strict projection equations
  and identifies `U`'s path coordinate with the transpose of edge 02 of this
  very filler `C`, using `stdSimplex.δ 1`. Hence it renders exactly the specified
  pair `(u e_r,c)`, rather than an unconstrained map of the two pullbacks.
- For each vertex `s`, the existential `φ` uses the existing `homotopyFiber`
  models. The equation `homotopyFiberToMappingPath r s ≫ U = φ ≫ ...` makes
  `φ` the actual restriction of `U` to the strict fiber.
  `mappingPathFiberWitness H C s φ` gives its first-coordinate equation and a
  triangle `t` that is explicitly equal to the transpose of the restriction of
  `C` along `homotopyFiberToMappingPath r s`. Its faces 01, 12, and 02 are
  respectively `H` at the first coordinate, the transported fiber path, and
  `φ`'s path coordinate. The witness therefore retains the same coherent
  composite as the prescribed filler in every simplicial degree.
- The second main conjunct quantifies any horn with the two prescribed edges
  and any two fillers `C₀,C₁` extending it. For the associated maps `U₀,U₁`,
  specified by `mappingPathInducedBy` for the respective fillers, it supplies
  `F : (mappingPath r ⊗ Δ[2]) ⊗ Δ[1] ⟶ T`. Its `ι₀` and `ι₁` restrictions
  are the two fillers; the horn restriction is `constantAlongInterval h`.
- `K : SSet.Homotopy U₀ U₁` has path coordinate
  `mappingPathCylinderEdge F`. This definition restricts `F` to 02 and switches
  the path and time interval factors before currying. Thus `K` is supplied by
  that very relative homotopy. Its projections to `Y` and `T` are explicitly
  `constantAlongInterval (mappingPathSource r ≫ u)` and
  `constantAlongInterval (mappingPathProjection r ≫ v)`.
- The final quantification over `s` and fiber restrictions `φ₀,φ₁` gives
  `L : SSet.Homotopy φ₀ φ₁`. The equation after composing `L.h` with the fiber
  inclusion identifies it with the restriction of `K.h` for the entire interval.
- `mappingPathRealizedComposition C` supplies the node's last, topological
  clause for every parameter vertex `a`. The three paths have continuous maps
  equal to `mappingPathRealizedEdge` of the actual 01, 12, and 02 restrictions
  of `C` at `a`. That definition uses `SSet.toTop.map` and Mathlib's canonical
  homeomorphisms for the realization of `Δ[1]` and its increasing unit-interval
  parametrization. `p₀₂.Homotopic (p₀₁.trans p₁₂)` means homotopy relative to
  both endpoints, since Mathlib's `Path.Homotopy` is `HomotopyRel ... {0,1}`.
  The horn equations identify 01 with `H_x` and 12 with `vγ`. The existential
  endpoints and paths do not weaken this: their continuous-map equalities
  completely specify the three paths.
- There is no weak-equivalence assumption on `u,v`, no fibration assumption on
  `r,q`, and no nonemptiness or connectedness assumption.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.homotopyFiber`, `commaSubcomplex`, `evaluation`,
  `constantDiagrams`. Mathlib's `SSet`, standard simplices, horns, internal
  hom, Kan condition, and geometric realization are its primitive notions.
- `Sheaf.AlgebraicTopology.KanFibrationFiberCriterion`:
  `SSet.Enhanced.mappingPathSubcomplex`, `mappingPath`, `mappingPathProjection`.
- `Sheaf.AlgebraicTopology.PathFibrationReplacement`:
  `SSet.Enhanced.homotopyFiberToMappingPath`. Its recorded theorem identifies
  this canonical inclusion with the strict fiber by an `IsPullback` square.
- `Mathlib.AlgebraicTopology.SimplicialSet.Homotopy`: `SSet.Homotopy` and its
  endpoint restrictions.
- `Mathlib.AlgebraicTopology.SimplicialSet.TopAdj`:
  `SimplexCategory.toTopHomeo`; `stdSimplexHomeomorphUnitInterval` is the
  existing increasing parametrization, with vertices 0 and 1 checked in source.
- `Mathlib.Topology.Homotopy.Path`: `Path.Homotopic`, `Path.trans`.
- Proof-only import:
  `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct`,
  whose `SSet.innerAnodyneExtensions_pushoutObjObjι'` is the exact recorded
  Mathlib match of `lem-coef-inner-anodyne-pushout-product` (full signature read).

The item's `stmt_deps` gains the already landed nodes
`lem-cbc-kan-fibration-fiber-criterion` and
`lem-coef-space-path-fibration-replacement`, because the statement directly uses
these owners' existing canonical constructions. Their modules are imported
through `PathFibrationReplacement`; neither dependency is restated or modified.
All additional predicates and coordinate maps in this module belong to the
mapping-path rectification notion and are listed in `lean.declarations` with
source and blueprint docstrings. There are no new independent notions or nodes.

Edge cases checked against the full statement: empty `X` makes `E_r` empty;
empty `S` forces `X` empty; empty `T` forces `S` and `Y` empty. Vertex and
realization assertions are then vacuous where appropriate. Empty strict fibers
remain valid sources of the fiber maps and homotopies. For the one-point target
all path clauses specialize to constant paths. A discrete target admits only
constant edges and the same formula remains meaningful. Nontrivial loop spaces
show why uniqueness must concern maps induced by the specified fillers, rather
than all maps satisfying only the two projection equations.

Search evidence retained from the saved packet (`searches.jsonl`):
`msearch.py ... leanfinder`, query "A homotopy square of Kan complexes is
rectified using mapping path spaces and coherent composition", returned
truncated-homotopy-square and relative-homotopy API, with no exact theorem.
`msearch.py ... loogle '\"Homotopy\", \"path\"'` returned homological-complex path
objects, with no simplicial square statement. `msearch.py ... grep
'mappingPath|mapping_path|rectif|homotopy.*square' AlgebraicTopology/SimplicialSet`
returned no matches. The earlier LeanSearch query "Mapping path replacement
makes a homotopy square of Kan complexes strictly commute" returned model-category
and ordinary-square declarations, with no full match. The saved report's `rg`
checks of upstream and side sources found and reused the mapping-path objects.
In this repair, `rg` over Mathlib, upstream `WeilConjectures`, and side `lean/Sheaf`
found no declarations for `mappingPathInducedBy`, `mappingPathCylinderEdge`,
`mappingPathRealizedEdge`, `mappingPathRealizedComposition`, `mappingPathSource`,
or `mappingPathFiberWitness`. The canonical realization and path-homotopy API
was read directly; no duplicate realization or path definition was introduced.

Validation: the repaired module compiles through the prescribed `scompile.py`
in both its sandbox and library paths with no errors or warnings. All variables
and universes are explicit (`autoImplicit false`); lines are at most 100 columns.
The one theorem has `sorry` as its entire proof and its docstring gives all seven
DAG proof steps, including the two pushout-product applications and the explicit
convex-interpolation proof of the realized-path clause. The required dry run and
final delivery are run on this packet after synchronizing `lean.statement` with
the exact theorem signature.

No mathematical node fault or `STATEMENT-DISPUTED` remains.

## Second reading by NM

This section records the worker's self-check of the retained packet and repairs;
the maintainer supplies the independent review. I opened the full mathematical
node and Lean module together. The saved Lean did not cover every filler, did
not constrain the two maps in the uniqueness clause to be induced by those
fillers, did not tie the coherent fiber triangle to that same filler, omitted
the realized endpoint-relative path comparison, and lacked the seven-step
proof docstring. Those defects are repaired above. In particular the previous
uniqueness claim for arbitrary maps with the two projection equations was too
strong: for a nontrivial group nerve as `T`, a point source and constant base,
different loop classes give such maps without a homotopy fixing both endpoints.
The mathematical node itself only claims uniqueness for the composites induced
by its fillers, which is what the repaired `mappingPathInducedBy` premises say.

I checked the four Kan binders, the orientation of `H`, both horn edges, the
universal filler quantifier, all three coordinates defining `U`, the restricted
triangle, the relative cylinder and its two endpoint equations, the link between
its 02 edge and `K`, both constant projections, restriction of `K` to every
fiber, and the realized 02 versus 01-then-12 homotopy. The explicit interval
factor switch in `mappingPathCylinderEdge` sends `(path,(a,time))` to
`((a,path),time)` before evaluating `F`. The real edge parametrization sends
0 to vertex 0 and 1 to vertex 1, so `Path.trans` has the node's stated order.
The strict-fiber assertions use the canonical inclusion already recorded by the
path-fibration node. No hypothesis or clause of the mathematical node is lost.
