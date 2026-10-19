## Worker report

Stage 2 now states `lem-coef-twisted-arrow-left-fibration` in
`lean/Sheaf/CategoryTheory/TwistedArrowLeftFibration.lean`, with principal declaration
`SSet.Enhanced.twistedArrow_left_fibration`. The DAG statement, dependencies, proof,
source, and stage-1 review are unchanged. The previous worker's stale-dispatch
diagnosis confused the landed Q48 stage-1 split with a stage-2 binding: the current
node has no `lean` field. This delivery supplies that field and its module.

The definitions have real data. Four named theorems have `sorry` proofs:
`twistedOrdinal_relations`, `twistedSource_naturality`,
`twistedTarget_naturality`, and `twistedArrow_left_fibration`. The first three
are precisely the construction's functoriality/restriction proof obligations
from Step 1, not additional mathematical prerequisites. Each has a source,
blueprint tag, and complete proof plan in its docstring. They are listed with
the main theorem in `lean.declarations`; no definition contains `sorry`.

The statement correspondence, in the order of the node, is as follows.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Simplicial sets and a quasicategory C | `C : SSet.{u}` and `[Quasicategory C]` in the mathematical conclusion; the construction families themselves are defined for all simplicial sets. No nonemptiness or other hypothesis is imposed. |
| Opposite has reversed faces and degeneracies | Mathlib `SSet.opFunctor` / `C.op`, with the existing `SSet.op_δ` and `SSet.op_σ` formulas; its ordinal operator is `SimplexCategory.rev.map`. |
| Ordered join `[n]ᵒᵖ ⋆ [n]` | `twistedOrdinal n = AugmentedSimplexCategory.tensorObjOf n n`. The first block is increasingly enumerated in reverse label order, and every first-block vertex precedes the second block. Its nerve is the standard `(n+n+1)`-simplex. |
| Twisted-arrow n-simplices are maps from the nerve of that join | `twistedArrow C = twistedOrdinalFunctor.op ⋙ C`. Yoneda identifies `C _⦋n+n+1⦌` with exactly those maps, including degenerate simplices. |
| Operator is precomposition with `θᵒᵖ ⋆ θ` | `twistedOrdinalMap θ = tensorHomOf (SimplexCategory.rev.map θ) θ`; contravariant application by `C` in `twistedArrow`. |
| Restriction to the two blocks and coupling λ | `twistedSource` and `twistedTarget` apply `C.map` to Mathlib `inl'` and `inr'`. `twistedProjection` pairs them using the actual degreewise cartesian tensor product. |
| λ is a left fibration | `leftFibration (twistedProjection C)`, the exact recorded predicate, testing every horn of dimension at least one and every `i < n`. `Quasicategory (twistedArrow C)` also records the implied domain condition. |
| Coslice consists of maps `Δ[0] ⋆ Δ[n] → C` fixed at x | `joinCoslice C x` is `(joinSlice (Δ[0] → C.op)).op`. Reversing the ordered join changes `Δ[n] ⋆ Δ[0] → C.op` into `Δ[0] ⋆ Δ[n] → C`; the outer opposite reverses the free parameter so its operators are the stated restriction operators. It reuses the recorded join slice, not a copied slice definition. |
| Coslice projects to the last block | `joinCosliceProjection` is the opposite of the existing slice projection followed by the existing double-opposite isomorphism. |
| First fixed-coordinate pullback | `twistedSourceFiber C x` is the existing `fiber (twistedSource C)` at x in `C.op`; its inclusion is the second categorical pullback projection. This is precisely `{x} ×_{C.op} Tw(C)`. |
| Collapse the first block | The existential `source C x` is constrained in every degree, after its pullback inclusion, to be `C.map (twistedCollapseFirst n.unop).op (joinCosliceSimplex C x n s)`. `twistedCollapseFirst` concatenates the constant first-block map with the identity second-block map. |
| The source comparison is an equivalence of quasicategories over C | `IsFunctorEquivalence (source C x)`, quasicategory assertions for its domain and codomain, and `source C x ≫ twistedSourceFiberInclusion C x ≫ twistedTarget C = joinCosliceProjection C x`. This uses the recorded coherent-inverse notion, not weak equivalence of realizations or equivalence of homotopy categories. Equivalences in the infinity-category slice are detected on underlying functors. |
| Dual comparison from `(C_/y).op` | `target C y` has exactly the opposite of the recorded join slice as its source. `twistedTargetFiber C y` is the target-fixed strict pullback. The point factor is written first using the dependency's `fiber` convention; swapping pullback factors canonically gives `Tw(C) ×_C {y}`. |
| Collapse the second block | Its every-degree formula evaluates the existing join slice on `joinPointTopSimplex`, then applies `C.map (twistedCollapseSecond n.unop).op`. That ordinal map is the identity on the first block and constant on the second. |
| The dual comparison is an equivalence over `C.op` | `IsFunctorEquivalence (target C y)`, the two quasicategory assertions, and the equation with `SSet.opFunctor.map (joinSliceProjection ...)`. No extra opposite is put on `Tw(C)`. |
| Both comparisons preserve identity-arrow vertices | The degree-zero clause exhibits a vertex representing `C.σ 0 x` in each slice model, and states that its comparison image, after inclusion, is exactly that same degenerate edge. The all-degree formulas determine every vertex image, so this is the actual identity vertex, not an arbitrary representative. |
| Constructions and maps commute with simplicial functors preserving chosen vertices | `twistedArrowMap` is postcomposition. `joinSlicePostcomp` and `joinCoslicePostcomp` are actual postcomposition maps, built from the recorded slice. The last three equations state naturality of λ and of both comparison maps for every `f : C ⟶ D`, with chosen vertices `f.app _ x` and `f.app _ y`. Equality after the pullback inclusion is naturality in that pullback because its point coordinate is unique. |

The two existential comparison families are not arbitrary maps substituted for
the canonical construction. Every simplex of each image is fixed by its ordinal
collapse formula, and the pullback inclusion is monomorphic. They therefore
determine unique maps. No object data is chosen from these unproved existence
claims; the construction definitions above them are independent of the theorem.
The same formulas are valid for all simplicial sets, as in the source construction;
the equivalence and fibration claims require exactly `[Quasicategory C]`.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsFunctorEquivalence`
  and its coherent-inverse/natural-equivalence definitions. Mathlib `SSet`,
  standard simplices, and `Quasicategory` are reused through that module.
- `Sheaf.CategoryTheory.InfinityFibrations`: `SSet.Enhanced.leftFibration` and
  `SSet.Enhanced.fiber`, including their full horn range and strict pullback convention.
- `Sheaf.CategoryTheory.JoinSliceRightFibration`: `JoinSliceSimplex`, `joinSlice`,
  `joinSliceProjection`, `joinPointTopSimplex`, and `joinSlice_right_fibration`.
  The stored base and all operator restriction equations are retained exactly.
- Mathlib `SimplexCategory.rev`, `AugmentedSimplexCategory.tensorObjOf`,
  `tensorHomOf`, `inl'`, `inr'`, `SSet.opFunctor`, `opObjEquiv`, and the
  double-opposite isomorphism supply the ordinal and opposite constructions.
- The stated proof dependencies `HomotopyEquivalenceWeak`, `RightPinchComparison`,
  `SliceEquivalenceFinal`, and `RealizationCylinder` are imported non-publicly.
  The three currently unstated proof dependencies (paired join horn, initiality
  of the identity in the twisted pullback, and the left-fibration initial-object
  criterion) have no modules to import. They are named in the main proof docstring.
  They are not statement prerequisites and no extra statement assumption is used.

Edge cases checked before writing:

- In degree zero `twistedOrdinal` is `[1]`; both collapse maps are the identity
  on that ordered interval. Source and target are its respective endpoints.
- For degree one the join is `[3]`, first-block labels decrease and second-block
  labels increase. The collapse maps have respective vertex sequences
  `(0,0,1,2)` and `(0,1,2,2)`, with the required reversed first-block operators.
- The empty quasicategory is allowed: twisted arrows are empty, there are no
  chosen-vertex cases, and left-horn lifting conditions are valid without adding
  nonemptiness. An empty mapping space is likewise not excluded.
- For a discrete category both fixed-coordinate slices and twisted fibers are
  points at each chosen vertex. For an ordinary category the first comparison
  identifies its coslice and the source-fixed twisted arrows, and the second
  identifies the opposite slice with the target-fixed arrows.
- The horn range includes `n = 1, i = 0`, and excludes `i = n` as required for
  left fibrations; no dimension-zero horn is introduced.
- `u` is explicit and arbitrary, and every simplex indexing category is small.
  The construction does not require a universe equality, finite mapping spaces,
  Kan-ness of C, or a choice of composition.

Searches for an existing declaration:

- `msearch.py leanfinder`, query: `Twisted arrow simplicial set projection left
  fibration coslice slice comparison`. Eight results, chiefly truncated nerve
  and simplicial-object facts; no twisted-arrow or slice-comparison declaration.
- `msearch.py loogle`, query: `"TwistedArrow"`. Zero results.
- `msearch.py grep`, query: `twisted.?arrow|edgewise`. Zero Mathlib results.
- `msearch.py leansearch`, query: `Twisted arrows of a quasicategory form a left
  fibration to the opposite times itself`. Eight results about opposite model
  structures and cofibrations, none about twisted arrows of a quasicategory.
- Direct `rg` for `twisted.?arrow|twistedArrow|edgewise` in the upstream
  `WeilConjectures` and published `lean/Sheaf` trees found no construction.
  The explicit item-id search in upstream `WeilConjectures` also found no match.
- Direct source search found Mathlib's ordinal concatenation and simplicial
  opposite APIs; their complete definitions and docstrings were read and reused.
- Candidate-name searches for `twistedOrdinal`, `twistedSource`, `twistedTarget`,
  `twistedArrow_left_fibration`, `joinCoslice`, and `joinSlicePostcomp` in Mathlib,
  upstream, and published side sources found no collision.

The cited sources were read online: [Kerodon 03JG](https://kerodon.net/tag/03JG)
for the join definition, [03JQ](https://kerodon.net/tag/03JQ) for the left
fibration, and [03K0](https://kerodon.net/tag/03K0) for the actual collapse
comparison over C. There is no statement correction or mathematical dispute.
No new node or dependency-record repair was needed.

Validation: the prescribed `scompile.py Q67 lem-coef-twisted-arrow-left-fibration`
compiled both its scratch presentation and named module cleanly (about 2–3
seconds each). The delivery dry run is the final worker check; no push is authorized
for the worker, and no second-reading section is written by the author.

## Second reading by Q67

I independently read the node's entire statement and seven proof steps against
`TwistedArrowLeftFibration.lean`, then opened the recorded dependency declarations.
Verdict: the Lean says exactly what this node says. No Lean or node repair was
needed; this reading adds the independent review and its validation record.
The sandbox node differs from the shared node only by its `lean` field; there
is no statement correction, new node, or dependency-module delivery to audit.
There is no maintenance repair note for this item.

Sources read independently online (this node cites Kerodon, not Stacks):
[03JG](https://kerodon.net/tag/03JG),
[03JK](https://kerodon.net/tag/03JK),
[03JQ](https://kerodon.net/tag/03JQ),
[03JL](https://kerodon.net/tag/03JL),
[03K0](https://kerodon.net/tag/03K0), and
[Section 8.1.2](https://kerodon.net/tag/03JV), including Construction the project server
and Example the project server. The construction allows any simplicial set; the fibration
and comparison equivalences require only a quasicategory. There is no standing
Kan, nonempty, finiteness, or additional size hypothesis. Construction the project server
specialized to a point is exactly first-block collapse; Example the project server repeats
the first vertex, as the Lean ordinal map does. Remark 03JL exchanges the two
projections through `Tw(C.op) ≅ Tw(C)`, without taking the opposite of `Tw(C)`.

Here is my object/hypothesis/conclusion checklist, in node order. Names in this
table are in `SSet.Enhanced` unless qualified.

| Node item | Lean rendering and second-reader verdict |
| --- | --- |
| Simplicial sets, operators, quasicategories, and arbitrary universe | Mathlib `SSet.{u}`, `SimplexCategory`, and `Quasicategory`. `universe u` is explicit and unrestricted. Correct. |
| Opposite has the same degree sets and reversed operators | Mathlib `SSet.opFunctor`, `opObjEquiv`, `op_δ`, and `op_σ`. I opened their implementations: operators apply `SimplexCategory.rev.map`, and `opObjEquiv` is the degreewise identity bijection. Correct. |
| C is a quasicategory | `(∀ (C : SSet.{u}) [Quasicategory C], ...)` governs precisely the fibration, quasicategory, and equivalence conclusions. No other instance is assumed. Correct. |
| Tw(C) in degree n is maps from N([n].op star [n]) | `twistedOrdinal n = tensorObjOf n n`, hence `[n+n+1]`; `twistedArrow C = twistedOrdinalFunctor.op ⋙ C`. Yoneda gives exactly these maps. First-block enumeration is reversed relative to its labels. Correct. |
| Operators precompose with theta.op star theta | `twistedOrdinalMap a = tensorHomOf (SimplexCategory.rev.map a) a`. I opened Mathlib's ordinal concatenation: it acts separately on the two blocks and preserves their order. Correct. |
| Restriction gives lambda to C.op times C | `twistedSource` uses `inl'`, `twistedTarget` uses `inr'`, and `twistedProjection` pairs them by the cartesian tensor. The source naturality has the opposite operator and the target has the original one. Correct. |
| Lambda is a left fibration | `leftFibration (twistedProjection C)` uses the recorded definition, all `n ≥ 1`, `i < Fin.last n`. The accompanying `Quasicategory (twistedArrow C)` spells out the claimed type of the construction. Correct. |
| Chosen vertex x and coslice maps Delta0 star Deltan into C fixed at x | `joinCoslice C x` is the opposite of `joinSlice` in `C.op` at x. Reversing the whole ordered domain turns Deltan star Delta0 into Delta0 star Deltan; the outer opposite reverses the free parameter, restoring its ordinary operators. This reuses the recorded join slice. Correct. |
| Coslice projection to the last block | `joinCosliceProjection` takes the opposite of the slice projection and then the double-opposite isomorphism. Its result is in C, as required. Correct. |
| Source-fixed pullback and collapse map | `twistedSourceFiber C x` uses recorded `fiber (twistedSource C)` at x in `C.op`; `twistedSourceFiberInclusion` is its pullback inclusion. The existential `source C x` has exactly this codomain. Its every-degree formula is precomposition with `twistedCollapseFirst`, constant on the first block and identity on the second. Correct. |
| Source comparison is an equivalence of quasicategories over C | Both domain and codomain quasicategory assertions, `IsFunctorEquivalence (source C x)`, and the equation with `joinCosliceProjection`. I opened `IsFunctorEquivalence`: it asks for a quasi-inverse and coherent natural equivalences. An equivalence over the base is detected on the underlying quasicategory functor. Correct. |
| Chosen y, opposite slice, target-fixed pullback | `target C y` starts at `(joinSlice (yonedaEquiv.symm y)).op` and ends at `twistedTargetFiber C y`. The dependency's point-first pullback is canonically the factor-swapped `Tw(C) ×_C {y}`. Correct. |
| Second-block collapse is the dual equivalence over C.op | The every-degree target formula applies `C.map (twistedCollapseSecond n.unop).op` to the slice extension's top simplex. This is identity on the first ordered block and constant on the second. Its equivalence and both quasicategory clauses are present, with the base equation to `opFunctor.map (joinSliceProjection ...)`. No extra opposite on Tw(C). Correct. |
| Both comparisons preserve the identity-arrow vertex | The two degree-zero existential clauses exhibit slice simplices representing `C.σ 0 x` and require their image after inclusion to equal the same degenerate edge. These are the identity vertices; they are not arbitrary vertices mapping to some identity. Correct. |
| Constructions/maps commute with functors carrying the vertices | `twistedArrowMap` is whiskered postcomposition; `joinSlicePostcomp` postcomposes extensions and bases; `joinCoslicePostcomp` is its opposite. The last three equations give naturality of lambda, source, and target for every f, with vertex image `f.app _ x` or `f.app _ y`. Equality after pullback inclusion suffices since the point coordinate is unique. Correct. |

The existential families precede the quasicategory hypothesis because the actual
collapse maps exist already for all simplicial sets. This does not add a
mathematical hypothesis or substitute arbitrary maps: the two formulas specify
the image of every simplex after a monomorphic inclusion, hence uniquely specify
the maps. No definition chooses data from the main existence theorem.

Dependency/interface checks: I opened
`EnhancedDiagramsCones` (`IsFunctorEquivalence`, `AreNaturallyEquivalent`,
`IsEquivalenceEdge`), `InfinityFibrations` (`leftFibration`, `fiber`), and
`JoinSliceRightFibration` (`JoinSliceSimplex`, `joinSlice`,
`joinSliceProjection`, `joinPointTopSimplex`, `joinSlice_right_fibration`).
Their signatures agree with their nodes and supply the actual notions used here,
including the unrestricted horn range, strict point fiber, and all-degree slice
restrictions. The extra stored slice base is uniquely determined by the extension;
the dependency theorem expressly records that uniqueness. No stronger auxiliary
condition enters this item. I checked the proof dependency records: all four
recorded proof modules are imported non-publicly; the paired-join-horn, initiality,
and initial-equivalence nodes still have no recorded Lean module. They are proof
steps, not missing objects needed to type this statement. The seven-step main
docstring retains the node's horn filtration, slice duality, initiality,
pinch/realization argument, comparison criterion, dual collapse, and naturality.

Edge cases independently checked:

- Degree zero: `twistedOrdinal ⦋0⦌ = ⦋1⦌`; both collapses are the identity
  ordinal map, so both comparisons preserve every represented arrow and in
  particular the degenerate identity edge. Endpoints have the correct order.
- Degree one: the ordered join is `[3]`; collapse-first has vertex sequence
  `(0,0,1,2)` and collapse-second `(0,1,2,2)`. A parameter map theta acts by
  `n-theta(m-i)` on the first block, exactly the opposite convention. After
  collapsing the second block, the opposite slice uses that same reversed theta.
- The empty quasicategory is allowed: Tw is empty and there are no chosen-vertex
  obligations. Left horn lifting is vacuous, without assuming nonemptiness.
  Empty mapping spaces and the discrete/terminal quasicategory cases are included.
- The fibration test includes the essential `n=1, i=0` case, excludes `i=n`,
  and imposes no dimension-zero horn. There are no rings, characteristic cases,
  scheme restrictions, or index-set assumptions in this statement.
- All universes and variables are bound. Finite ordinal indexing imposes no
  restriction on C's universe. C and D may be placed in a common containing
  universe, as in the node; no equality of separate site universes is imposed.

Independent H4 searches used different wording from the worker:

- `msearch.py ... leanfinder "Two sided edgewise subdivision of simplicial sets
  and its projection to opposite product"`: eight hits, involving simplicial
  product projections (`SSet.ι₀_snd`, `ι₁_snd`, and `prodStdSimplex`), not the
  edgewise construction, left fibration, or comparison.
- `msearch.py ... loogle '"edgewise"'`: zero hits.
- `msearch.py ... leansearch "The coslice inclusion into source fiber of twisted
  arrows is an equivalence of quasicategories"`: eight ordinary-category comma,
  join, and fiber equivalences, whose displayed types require ordinary categories
  and do not cover the node.
- Direct `rg -i` for `edgewise|twisted.?arrow|twistedArrow|coslice.*equival`
  over Mathlib, upstream `WeilConjectures`, and shared `lean/Sheaf`: no match.
  A broader `coslice` search found proof-docstring references and ordinary/Reedy
  category notions, not a simplicial coslice definition. I opened the DAG node
  `lem-cbc-relative-coslice-left-fibration`: it has no Lean record and concerns
  general relative coslices, not another published point-coslice implementation.
  I also checked the upstream name index: no candidate-name collision.

H5/H6/H8/H9: every definition contains actual data; construction proof obligations
are the three separately named theorems, each with source, blueprint tag, and
proof plan. Every theorem proof is exactly `sorry`; no theorem was proved in this
stage. Structure/functor law fields use routine proofs, not postponed data.
All declarations have source/blueprint docstrings; the main statement has all
seven proof steps. There are no private copies, local notation, local instances,
unbound variables, or lines over 100 characters. `lean.statement` was checked
verbatim equal to the signature extracted from the source. No mismatch found;
no statement or definition was rewritten.

Validation: the prescribed `scompile.py Q67
lem-coef-twisted-arrow-left-fibration
lean/Sheaf/CategoryTheory/TwistedArrowLeftFibration.lean` passed both sandbox
and library presentations cleanly (2.0 s and 2.5 s), with no diagnostics.
