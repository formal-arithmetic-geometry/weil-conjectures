## Worker report

The module `Sheaf.CategoryTheory.CoherentCartesianPostcomposition` states
`SSet.Pinched.coherent_cartesian_postcomposition`, with its entire proof `sorry`.
There are two explicit helpers belonging to this node: `coherentEdge` is just
endpoint transport of the existing canonical `edgeVertex`, and
`IsFunctorialKanHomotopyPullbackSquare` expands the node's strict square and
functorial Kan-replacement/path-space convention. Both have real definitions;
neither selects data from an unproved existence theorem. No mathematical statement
of the node is corrected.

The hypotheses correspond as follows:

| Node | Lean |
|---|---|
| Small quasicategories E and B | `{E B : SSet.{u}} [Quasicategory E] [Quasicategory B]`, with explicit universe `u` |
| Simplicial map p:E→B, an inner fibration | `(p : E ⟶ B) (hp : InnerFibration p)` |
| Arbitrary test vertex a | `(x : E _⦋0⦌)`; x is the node's a |
| Edge e:b→c | `(b c : E _⦋0⦌) (e : Δ[1] ⟶ E)`, with `he₀` and `he₁` the source and target equations |
| e is p-Cartesian | `he : Enhanced.IsCartesianEdge p e`, the recorded final-horn predicate |

The conclusion corresponds clause by clause:

| Node | Lean |
|---|---|
| Upper left and right corners | `hom (rigidification.obj E) (vertex E x) (vertex E b)` and the same expression with c |
| Lower left and right corners | `hom (rigidification.obj B) (vertex B (p.app _ x)) (vertex B (p.app _ b))` and the same expression with c |
| Upper row, enriched postcomposition by [e] | `enrichedPostcomposition ... (coherentEdge b c (SSet.yonedaEquiv e) he₀ he₁)` |
| Vertical maps induced by ℭ[p] | `mappingMap p x b` and `mappingMap p x c`; these are the existing enriched-functor mapping maps with canonical vertex transport |
| Lower row, enriched postcomposition by [p(e)] | `enrichedPostcomposition` in `rigidification.obj B`, with `coherentEdge` on `p.app _ (SSet.yonedaEquiv e)`; its endpoint proofs are naturality of p applied to the face maps |
| Strict commutativity of the displayed square | The first existential `w : f ≫ h = g ≫ k` in `IsFunctorialKanHomotopyPullbackSquare` |
| Functorial Kan replacement of the entire diagram | A functor R and natural transformation `r : 𝟭 SSet ⟶ R`; each component is a monomorphism and realization weak equivalence, and each `R.obj T → Δ[0]` is a Kan fibration |
| Canonical comparison to the path-space homotopy fiber product | `Enhanced.homotopyPullbackComparison (R.map f) (R.map g) (R.map h) (R.map k) ...`, with commutation obtained from w by `R.map_comp` |
| Comparison is a weak homotopy equivalence | The existing realization predicate `Enhanced.IsWeakHomotopyEquivalence` applied to that map |
| No Kan assumption on raw mapping sets | No such instance or hypothesis occurs; only the replaced objects have terminal Kan fibrations |

The replacement conditions express the usual factorization of each terminal map
as a trivial cofibration followed by a Kan fibration. The recorded Kan--Quillen
core identifies trivial cofibrations with weak monomorphisms. Thus this is a
replacement construction in the conclusion, not an extra hypothesis on E or B.
The existing comparison inserts the constant path at the strict common image and
uses the already defined `simplicialHomotopyPullback`, retaining higher simplices.

Dependencies read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, and its Mathlib reexports for simplicial
  sets, quasicategories and standard simplices.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`: publicly reexports
  `SSet.Enhanced.IsCartesianEdge` and Mathlib `SSet.InnerFibration`. The node's
  currently recorded `cocartesianFibrationOver` is unrelated to this Cartesian-edge
  use; its module retains the complete original edge interface.
- `Sheaf.CategoryTheory.CoherentNerveComparison`:
  `CategoryTheory.CoherentNerveComparisonStatement` and
  `CategoryTheory.coherent_nerve_comparison`, providing the comparison package for
  the proof plan.
- `Sheaf.CategoryTheory.RigidificationPostcompositionComparison`:
  `SSet.Pinched.edgeVertex` and `enrichedPostcomposition`; its publicly imported
  `Sheaf.CategoryTheory.PinchedRigidificationResolution` supplies
  `SSet.Pinched.rigidification`, `vertex`, and `mappingMap`. These are the existing
  simplex-colimit realization, canonical generator and induced mapping maps.
- `Sheaf.CategoryTheory.RelativeInfinityCone`:
  `SSet.Enhanced.homotopyPullbackComparison`.
- `Sheaf.AlgebraicTopology.KanQuillenModelRightProperCore`:
  `SSet.KanQuillen.right_proper_kan_quillen_core`, with the Mathlib Kan-fibration
  instance it uses. This explains the replacement conditions.

The last three already recorded DAG owners were added to `stmt_deps`, as allowed
by brief-stage2 section 5. The node copy otherwise changes only its `lean` record.
There is no dependency repair and no new independent definition node.

All currently stated proof dependencies are imported: the coherent-nerve module,
`InfinityCartesianMappingCriterion`, `InfinityKanHomotopyCoherentCubeInvariance`,
`KanFibrantPathRecognition`, and `KanHomotopyCartesianInvariance`.
`lem-cbc-coherent-square-comparison-data` currently has no Lean record and is
proof-only, so no import is invented for it. Its four-step use is retained in the
theorem's full natural-language proof docstring; this delivery states the theorem
and does not prove or assume that auxiliary theorem.

Edge cases checked mathematically before finalizing the statement:

- Empty E has no test vertex or edge, so its quantified cases are vacuous; no
  artificial nonemptiness is assumed. Mapping objects themselves may be empty.
- For p the identity, the square has identity vertical maps and gives the expected
  homotopy-pullback square for any edge.
- For B=Δ[0], Cartesian edges give the expected postcomposition equivalences in E.
- Degenerate Cartesian e, b=c, coincident test vertices, and empty source mapping
  objects are included; endpoint transport uses only equality proofs.
- No independent smaller universe or local Kan restriction has been imposed.

Searches were run with `msearch.py` and direct `rg`, before selecting the
declarations. The exact machine outputs are retained in sandbox `searches.jsonl`.

- LeanFinder, `Cartesian edge postcomposition coherent realization homotopy pullback square`:
  eight results, concerning truncated homotopy categories, relative simplicial
  homotopies, ordinary strongly Cartesian arrows and hypercovers. No exact theorem.
- LeanFinder, `homotopy pullback square simplicial sets Kan replacement path-space comparison`:
  eight results about model-category path objects and truncated simplicial homotopy
  categories. No coherent-realization Cartesian square theorem.
- Loogle, `"SSet", "cartesian"`: valid query, zero results. The other exploratory
  unquoted queries were rejected for unknown identifiers and are not absence evidence.
- Mathlib grep, `coherent.*cartesian|homotopy.*pullback` in `AlgebraicTopology`:
  two results in model-category `RightHomotopy.lean`, neither this theorem.
- Mathlib grep, `homotopy.*pullback|path.*space` in `AlgebraicTopology`:
  eighteen path-object/topological homotopy results, no exact statement.
- `rg` of the upstream `WeilConjectures` and project `lean/Sheaf` trees for
  Cartesian mapping, coherent realization, postcomposition, and the exact item id
  found the recorded rigidification construction and its postcomposition comparison,
  which are reused. `CartesianMappingSimplexMixedEquivalence` is only the specialized
  simplex-base weak-equivalence assertion; `InfinityCartesianMappingCriterion`
  concerns quasicategory mapping spaces, not the raw enriched square. Neither
  replaces this statement. Name searches of Mathlib, upstream, the project's Lean
  tree and `dag/lean_names_upstream.json` found no preexisting names for the three
  new declarations.

Source checked online in [Lurie's HTT](https://people.math.harvard.edu/~lurie/papers/HTT.pdf):
Proposition the project server, printed pp. 131--132/PDF pages 148--149, includes arbitrary
test vertices and notes the need to retain the whole square; Theorem the project server,
printed p. 89/PDF page 106, supplies the comparison framework. Proposition
the project server's proof, printed p. 184/PDF page 201, uses the actual enriched
postcomposition map. The IAS URL timed out; the author's Harvard copy was read.
No statement dispute or source-based correction was found.

Validation: `scompile.py` compiled the module separately as both its sandbox probe
and its named library module, with no errors or warnings. The only postponed
theorem is `SSet.Pinched.coherent_cartesian_postcomposition`.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
