# Stage-2 statement: lem-cbc-standard-simplex-mapping-contractible

## Worker report

The module `Sheaf.CategoryTheory.StandardSimplexMappingContractible` states the entire node as
`CategoryTheory.SimplicialThickening.standard_simplex_mapping_contractible`, with one `sorry`.
Its helper `standardSimplexLastEdge` constructs the endpoint-subset morphism for the last edge;
its data and all structure-field proofs are complete. No theorem is proved in this delivery.
No new DAG node, dependency repair, or statement correction is required. Only the item's `lean`
record changes.

The previous worker mistook Q10's completed stage-1 split for a completed stage-2 statement.
The inspected item is split and reviewed, but has no `lean` record. Q10's report explicitly says
there is no Lean attachment. This delivery uses the unchanged, reviewed five-step argument.

Hypotheses and clauses, in order:

- Standard simplices and their subset-poset coherent realizations are the existing
  `SimplicialThickening (ULift.{u} (Fin (r + 1)))`. These are precisely the categories in the
  recorded comparison's `CoherentNerveComparisonStatement.simplex_realization` field.
  `r : ℕ` covers every dimension, including zero; `i j : Fin (r + 1)` encode all vertices
  between zero and r. The only ordering hypothesis is `i ≤ j`.
- The first conjunct explicitly says `sHom (mk (ULift.up i)) (mk (ULift.up j)) =
  nerve (Path (ULift.up i) (ULift.up j))`. This is the node's identifying clause, not an
  additional conclusion. Mathlib's `Path.I`, `left`, `right`, `left_le`, and `le_right` give
  exactly the subsets contained in the closed interval and containing its endpoints.
  Its existing category is induced from the inclusion order on subsets. No poset is copied.
- The remainder of the first conjunct is `SSet.Enhanced.IsContractible` of that enriched hom.
  This existing definition is the weak equivalence of its unique map to the actual standard
  zero-simplex, using geometric realization, path components, and every positive based
  homotopy group. No Kan or ordinary contractibility hypothesis is added.
- The second conjunct has independently quantified dimensions `r s`, endpoint pairs `i j`
  and `k l`, and exactly their two ordering conditions. It quantifies over every simplicial
  map `f` between the enriched homs and concludes the recorded
  `SSet.Enhanced.IsWeakHomotopyEquivalence f`. Thus maps between different dimensions and
  different endpoints are included, not merely functor-induced maps.
- The third conjunct reindexes the node's positive dimension as `r + 1`. Its
  `i : Fin (r + 1)` has image `i.castSucc : Fin (r + 2)`, exactly all vertices at most r.
  The source endpoint is `(Fin.last r).castSucc` (value r); the target endpoint is
  `Fin.last (r + 1)` (value r+1). The term `eHomWhiskerLeft SSet ...
  (standardSimplexLastEdge r)` is the canonical enriched postcomposition map between
  precisely these homs. The constructed edge's underlying subset is literally the pair
  of endpoints. By the existing thickening's composition, this map takes S to
  `S ∪ {r,r+1}`, as required. There is no arbitrary replacement map or existence choice.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsContractible` and
  `SSet.Enhanced.IsWeakHomotopyEquivalence` (including their realization-based definitions).
- `Sheaf.CategoryTheory.CoherentNerveComparison`: the full signature of
  `CategoryTheory.coherent_nerve_comparison` and the
  `CoherentNerveComparisonStatement.simplex_realization` and `simplex_maps` fields identify
  the exact thickening construction used here. This recorded statement dependency is
  publicly imported. Its other conclusions are not extra hypotheses of this theorem.
- `Mathlib.AlgebraicTopology.SimplicialNerve` (via the recorded comparison import):
  `CategoryTheory.SimplicialThickening`, `Path`, its induced category, and the simplicial
  enrichment (nerve homs, union composition); their full defining source was read.
- Mathlib's `SimplicialCategory.sHom` and `EnrichedOrdinaryCategory.eHomWhiskerLeft` give
  the existing enriched hom and actual postcomposition; both signatures and definitions
  were read, rather than reconstructing either operation.
- Proof-only import `Sheaf.CategoryTheory.SimplicialHomotopyEquivalenceWeak` supplies
  `SSet.Enhanced.simplicial_homotopy_equivalence_weak`. Its full theorem and proof-plan
  docstring were read. This is the third recorded proof dependency; the other proof
  dependencies are already the public imports.

Source check: read Lurie's online Higher Topos Theory, Definition 1.1.5.1, Remark 1.1.5.2
(printed pp. 20-21, PDF indices 37-38), and Proposition 3.2.2.10 and its mapping diagram
(printed pp. 183-184, PDF indices 200-201). The first definition gives exactly the
endpoint-subset nerves and union composition; the remark identifies the endpoint-pair
edge vertices and states weak contractibility. The arbitrary-map consequence is the
component/group cancellation written in Q10's unchanged DAG proof. The entire five-step
proof, including the degreewise cylinder formula and correct image basepoints, appears
in the theorem docstring. No text is changed to make formalization easier.

Edge cases checked: r=0 forces i=j=0 and gives a one-object subset poset; every i=j gives
the singleton subset poset; adjacent endpoints also give a point. For dimension two and
endpoints 0,2, the poset is `{0,2} ⊂ {0,1,2}`, so its nerve need not be Kan; no Kan assumption
is made. For dimension three, endpoints 0,3 give the square nerve. In the final clause,
r=0 represents the original dimension one and yields point-to-point postcomposition;
i=r represents a point source in every positive dimension. Two different simplex dimensions
are explicitly permitted. The unordered, empty hom cases i>j are excluded by exactly the
node's i≤j hypothesis. Universe u is explicitly bound and arbitrary, and `ULift.{u}` follows
the recorded coherent-realization interface; all these finite sets live in every such universe.

Searches actually executed:

- `msearch.py ... leanfinder "Mapping simplicial sets of the coherent realization of a standard
  simplex are nerves of endpoint subset posets and weakly contractible"`: eight hits,
  including `SSet.stdSimplex.isoNerve`, `SimplicialNerve`, ordinary nerve results, and KanComplex.
  No hit is the contraction or all-maps theorem. Read the thickening and nerve source.
- `msearch.py ... leansearch "Any simplicial map between mapping objects of the coherent
  realization of standard simplices is a weak homotopy equivalence"`: eight hits, on simplex
  realization, simplex maps, ordinary simplex nerves, truncated homotopy categories, and
  cofibrant-object localization. None states the requested mapping-set theorem.
- `msearch.py ... loogle "CategoryTheory.SimplicialThickening.Path,
  SSet.Enhanced.IsContractible"`: unknown second identifier; unavailable query, not evidence
  of absence. Repeated with `"CategoryTheory.SimplicialThickening.Path"`: twelve hits give
  `Path`, its fields, constructor, extensionality, induced category and union formula.
  These give the existing objects but not their weak contractibility.
- `msearch.py ... grep "contractib|weakEquivalence" AlgebraicTopology/SimplicialNerve.lean`:
  zero hits. The whole file was read to verify the defining models.
- `rg` of the upstream `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id, `Thickening.*[Cc]ontract`, `[Cc]ontract.*Thickening`, and
  `standard_simplex_mapping`: no hits.
- `rg` of Mathlib, upstream, and project sources for `standardSimplexLastEdge`,
  `standard_simplex_mapping_contractible`, last-edge postcomposition and last-edge definitions:
  only the unrelated `moduleSectionLastEdges` in `CoherentModuleSectionModel` was found and
  inspected. It packages edge data of module-valued sections, not an endpoint-subset edge.

Validation: the prescribed scompile wrapper compiled the sandbox check and exact library
module cleanly (10.8 s and 29.3 s respectively), with no warnings or errors. The signature
record was extracted verbatim from the module; every line is at most 100 characters.
The delivery wrapper repeats compilation and runs the server preflight before its push.
No direct Git operation, live-library edit, or global build is used.

## Second reading by NB

Independent maintainer reading of immutable delivery
`6679fbf86637424456a9877ccab604ef1831ca27`, performed 2026-10-17.
This section replaces the delivered placeholder; the reviewer did not author the delivery.

I read packet.md, the item JSON, both statement-dependency JSON records, the delivered
module, its docstrings and this report. I read HTT Definition 1.1.5.1 and Remark 1.1.5.2
(printed pp. 20–21, PDF indices 37–38), and Proposition 3.2.2.10 with its mapping square
(printed pp. 183–184, PDF indices 200–201), at
https://www.math.ias.edu/~lurie/papers/HTT.pdf . The latter uses the more general mapping-simplex
calculation; its Cartesian-fibration hypotheses are not hypotheses of this standard-simplex
lemma. The defining subset-poset calculation and endpoint vertices are in 1.1.5.1–1.1.5.2.

Clause-by-clause reading:

- `r : ℕ` and `i j : Fin (r + 1)` give exactly every dimension and vertex pair;
  `i ≤ j` is exactly the required ordering hypothesis.
- `sHom (mk (ULift.up i)) (mk (ULift.up j))` is the existing enriched hom of
  `SimplicialThickening`, the standard-simplex realization specified by the dependency's
  `CoherentNerveComparisonStatement.simplex_realization`. Its `simplex_maps` uses the same
  monotone-map action. No arbitrary simplicial category is substituted.
- The first equality identifies the hom with `nerve (Path ... ...)`. Mathlib's `Path`
  has subset data `I`, endpoint membership `left`, `right`, and interval bounds
  `left_le`, `le_right`; its category is induced from inclusion of subsets. The existing
  simplicial enrichment sets its hom to this nerve and composition to union.
- `SSet.Enhanced.IsContractible` is the weak equivalence of the unique map to the
  actual zero-simplex. `IsWeakHomotopyEquivalence` uses bijectivity on realized path
  components and every positive based homotopy group, at every source basepoint.
  These are exactly the node's notions; neither Kan fibrancy nor nonemptiness is assumed.
- The second conjunct quantifies independently over dimensions `r s`, both ordered
  endpoint pairs, and every simplicial map `f`. It therefore includes different
  dimensions, with no restriction to maps induced by enriched functors.
- The last conjunct writes the original positive dimension as `r + 1`.
  `i.castSucc` ranges over precisely the vertices at most r; the edge endpoints are
  `(Fin.last r).castSucc` and `Fin.last (r + 1)`. The helper constructs their two-element
  subset. `eHomWhiskerLeft` is the existing enriched postcomposition, defined using
  the morphism's enriched vertex and enriched composition. Here it sends S to
  `S ∪ {r,r+1}`. This is the canonical arrow in the node, including its direction.

I checked the exact declarations in the read-only group clone:
`EnhancedDiagramsCones.lean:74–102` (components, based groups, weak equivalences and
contractibility), `CoherentNerveComparison.lean:193–204,318–320` (realization fields
and recorded theorem), and `SimplicialHomotopyEquivalenceWeak.lean:75–83` (the
proof-only homotopy-equivalence theorem). Mathlib's `SimplicialNerve.lean:58–140`,
`SimplicialSet/Nerve.lean:35–40`, `SimplicialCategory/Basic.lean:58–65`, and
`CategoryTheory/Enriched/Ordinary/Basic.lean:97–99` supply the exact constructions used.
The theorem on simplicial homotopy equivalences requires both cylinder homotopies,
allows either orientation independently, and has no Kan hypothesis. The least-element
contraction supplies these with the point map and least-element vertex.

All five proof-plan steps agree with the DAG: the least subset is `{i,j}`; the
zero/one cylinder formula remains a chain and commutes with arbitrary monotone
restrictions; its endpoints give the homotopy inverse; cancellation uses the image
basepoint in the target; union with the last edge is the specified postcomposition.

Edge cases checked: dimension zero; i=j; adjacent endpoints; dimension two with
endpoints 0,2 (the interval nerve, not generally Kan); dimension three with endpoints
0,3 (the square nerve); dimension one in the final clause; and i=r in that clause
(point source). Unordered endpoints are excluded exactly as in the statement.
`autoImplicit false` and the explicit arbitrary universe u leave no unbound variables
or silent universe equalities. The finite `ULift` realization works in every u.

I independently searched Mathlib's AlgebraicTopology, upstream WeilConjectures and
the group's lean/Sheaf using `rg` for thickening/weak/contract combinations,
subset/nerve/least combinations, and last-edge constructions. I inspected the nearby
`CoherentRealizationBeadNormalForm`, `MappingSimplexUniversalEquivalence`, and
`InitialPosetSliceRestriction` declarations: they concern flags, a comparison over
an arbitrary base, and join-slice restriction, respectively, not this theorem or edge.
The reported LeanSearch, LeanFinder, Loogle and grep searches are recorded; failed
Loogle queries are explicitly marked unavailable. No exact duplicate was found.
The module reuses the existing Path, nerve, enrichment and realization predicates.

Mechanical and maintainer gates: the node's `lean.statement` matches the signature
byte for byte. Its record lists both declarations and the correct module/file/branch;
both statement dependencies are publicly imported and the proof-only dependency is
privately imported. There is one postponed theorem, with proof exactly `by sorry`.
The helper contains actual subset data and complete structure-field proofs, with no
postponed data or proof obligation. No mathematical theorem is locally proved.
All declaration/source/blueprint docstrings are present and the theorem docstring
carries the complete five-step proof. Every Lean line has at most 100 characters.
There are no new nodes, dependency repairs or statement corrections, so no §1(C)
citer audit is needed. The lemma is simplicial, and uses no pro-etale substitute.

Reproduced compile, using only the prescribed wrapper:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NB
lem-cbc-standard-simplex-mapping-contractible
snapshot/lean/Sheaf/CategoryTheory/StandardSimplexMappingContractible.lean`.
The current wrapper dispatched to the server's private side overlay: sandbox check
1.6 seconds, exact library module 1.5 seconds, exit code 0, no diagnostic warnings
or errors. This independently confirms the worker's recorded clean per-file compile;
the elapsed times naturally differ. The documentation-only replacement module was
also compiled through this wrapper; its result is recorded in review.md.

Findings and repairs: H11 (also the substantive report requirement in H1): the
original second-reading section explicitly said no reading had occurred. Replaced it
with this actual independent reading. Corrected the worker report's garbled source
names, which read “the project server,” to the exact numbered HTT references.
H8/§3 convention: added the module-level main-definition/main-statement list for its
two declarations. These are documentation repairs only; no Lean signature, data,
proof, dependency, or node statement changed. No fault in mathematical substance found.
No repository, branch head or live Lean source was modified; no global build ran.
