## What changed

Reduced `AlgebraicGeometry.Etale.exists_etale_complex_abutment_presentations` to the
categorical, coherent stationary-page interface
`AlgebraicGeometry.Etale.exists_etale_complex_coherent_filtrations` in the new module
`Sheaf.AlgebraicGeometry.EtaleComplexCoherentFiltrations`.
The original statement and all existing visibility are preserved. The first-page
reindexing theorem remains unchanged.

The proof constructs a directed final reindexing with Mathlib, defines S and the
stage T as actual additive ranges of transported subobject inclusions, and uses
injective range equivalences and categorical cokernel projections to construct q
and t. Cokernel exactness proves the kernel clause, epimorphy proves surjectivity,
and the explicit restriction/naturality squares prove membership and the final
equality. Both filtration bounds, including p<a and filtration length zero, are
transported in Lean. No object is defined by arbitrary choice from an unproved
mere-existence theorem. The local range equivalences invert injective maps; their
inverse values are uniquely determined.

Proof imports added: `Sheaf.AlgebraicGeometry.EtaleComplexCoherentFiltrations`,
`Mathlib.CategoryTheory.Presentable.Directed`, `Mathlib.CategoryTheory.Category.ULift`,
`Mathlib.Algebra.Homology.ShortComplex.Ab`, and `Mathlib.CategoryTheory.Abelian.Exact`.
The new module publicly imports the existing complex-term cohomology interface and
`Sheaf.CategoryTheory.Filtration`, which its statement needs. As plain proof imports
it also retains the modules of its DAG plan:
`Sheaf.CategoryTheory.HypercohomologyFirstPage`,
`Sheaf.CategoryTheory.KInjectiveBridge`,
`Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`,
`Sheaf.AlgebraicGeometry.EtalePresentationImageFiltration`,
`Sheaf.AlgebraicGeometry.EtaleHypercohomologyFiltration`, and
`Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial`.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Etale.exists_etale_complex_abutment_presentations`
(node `lem-weil-pbc-etale-complex-abutment-presentations`).
The original `reindex_first_page_comparison` was already proved.

Added exactly one hole:
`AlgebraicGeometry.Etale.exists_etale_complex_coherent_filtrations`
(node `lem-weil-pbc-etale-complex-coherent-filtrations`).
There are no remaining sorries in the assigned module. This is a decomposition,
not a net hole reduction: one hole closed and one hole added. The new theorem
only supplies categorical filtration and stable-page data. It supplies no
reindexing, no H/eH/B/eB, no subgroup S or T, no quotient homomorphisms, and none
of their kernel, surjectivity, or transported cocone equations. Those constructions
and verifications form the complete Lean proof in the assigned module.

## No longer needed

Both original public imports remain necessary for the unchanged statements and
first-page reindexing theorem. Removed these six original proof imports from the
assigned module:

- `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`
- `Sheaf.CategoryTheory.ExistsDirectedReindexing`
- `Sheaf.CategoryTheory.HypercohomologyFirstPage`
- `Sheaf.CategoryTheory.KInjectiveBridge`
- `Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`

The new coherent-filtrations module imports the modules of its stated proof
plan as plain proof imports. Its two public imports provide only the declarations
used in its signature. `LowerShriek` is already publicly available through the
unchanged term-cohomology interface.

All seven old direct proof dependencies disappear from the assigned node:
`def-sp-kinjective-bridge`, `def-sp-spectral-sequence`,
`def-weil-pbc-etale-cohomology`, `lem-weil-pbc-filtered-category-directed-cofinal`,
`lem-weil-pbc-hypercohomology-e1-pullback-functorial`, `thm-sp-if-e1`, and
`thm-sp-spectral-object-yields`. The new node retains the relevant spectral and
functoriality dependencies; étale cohomology is a statement dependency there.
This is direct-dependency pruning, not a claim that those shared modules leave
the entire targets' import closure.
The existing private helpers `step_quotient_zero_iff` and `cokernel_map_apply`
in `Sheaf.AlgebraicGeometry.EtaleComplexFiltrationPageData` are unavailable across
module boundaries. Their short categorical proofs are local `have` terms inside
the target proof, so no duplicate library declarations are introduced.
The DAG dependency `lem-weil-pbc-filtered-category-directed-cofinal` and its module
`Sheaf.CategoryTheory.ExistsDirectedReindexing` are not needed on this proof route:
Mathlib's `IsFiltered.exists_directed` directly provides a final directed reindexing.
No other original dependency is claimed globally pruned: the new coherent-interface
node still needs the original hypercohomology and convergence theory. Its imported
statement uses the already-defined filtration and cohomology interfaces.

## Where the brief, the DAG or earlier work was wrong

The proof plan describes one coherent choice of pages and filtrations at every
filtration degree. `exists_etaleComplex_uniform_pages` instead quantifies q before
its existential diagram/presentations. Applying it separately at each q cannot
supply a single E0 and E' for this theorem. The new node records exactly the missing
categorical coherence/convergence step; it is not a renamed subgroup-presentation
conclusion. No existing signature is changed or disputed.

The blueprint unit record `sk-prop-h2` has empty realized statement/step lists, and
this delivery changes no unit or chapter route.

The local literature payload is absent in this clone. Read the primary source online:
[015J](https://stacks.math.columbia.edu/tag/015J),
[015K](https://stacks.math.columbia.edu/tag/015K), and
[0EZM](https://stacks.math.columbia.edu/tag/0EZM).
LeanFinder returned homological boundedness lemmas, but no coherent diagram interface.
Loogle found `CategoryTheory.IsFiltered.exists_directed`; local
Mathlib/library searches found the categorical cokernel and directed-final APIs.
LeanSearch was attempted for the coherent interface and was unavailable with an
Internal Server Error; no verdict is inferred from that unavailable search.

## New nodes

`lem-weil-pbc-etale-complex-coherent-filtrations`, in
`dag/nodes/sec-curve-estimates/`, states the categorical part of steps 1, 3, and the
restriction part of step 4 of the original plan. One spectral-sequence diagram and
one family of categorical filtrations work at all q, with a stationary page
allowed to depend on q. Its source/proof describes first-page support,
common stationary-page bounds, the target filtration bounds at a and max(a,p+1),
and cokernel naturality. Edge cases checked: negative resolution/complex bidegrees,
zero complexes, p<a, p=a-1, and q outside the support region. The maximum in the
upper filtration bound handles zero-length filtrations. No change records or
forced adaptations are needed.

Validation: both modules checked with the required single-file compiler. The final delivery
dry run passed; the second reader performs the requested delivery after review.

## Earlier second reading (a previous round; superseded)

1. Compared both delivered modules with the repository versions. Existing declaration signatures and visibility are unchanged; only the proof, imports, and the new split-off interface/node were added.
2. Compiled the coherent-filtrations module successfully. The abutment-presentations module elaborates to a generated `.olean`, but the local 60-second compiler gate timed out under concurrent machine load; no Lean diagnostic was emitted.
3. Checked the sole split-off theorem: it is the categorical coherent-filtrations interface, strictly weaker than the target and needed by the proof. Its docstring, DAG node, and edge-case discussion are present; no definition contains `sorry`.
4. The proof follows the coherent stationary-page route, constructs the filtrations and quotient maps explicitly, and uses Mathlib directed-final and cokernel APIs. The old directed-reindexing dependency is pruned from imports and node dependencies.
5. The unit route is preserved: the coherent filtration node realizes the categorical part of the planned route, while the target module supplies the remaining reindexing and presentation construction.

Changed during second reading: no proof or statement changes were necessary. The report was updated with this review and the local timeout limitation.

## Second reading by D2

1. **Interface comparison — pass.** Read both delivered modules and diffed the
   assigned module against the repository. The complete signatures of
   `reindex_first_page_comparison` and
   `exists_etale_complex_abutment_presentations` are byte-for-byte identical.
   The existing node changes only `proof`, `proof_deps`, and `proof_origin`.
   No definition, existing visibility, or target statement changes, and no
   change record or forced adaptation is needed.
2. **Proof and data — pass.** Read the cokernel kernel proof,
   the injective range equivalences, the directed-final construction, and each
   transport equation. `S`, `T`, `q`, and `t` are actual constructions in the
   theorem proof. The only `sorry` is the named new coherent-filtrations theorem;
   there is no holed definition and no forbidden declaration. The main proof
   compiled in an instrumented scratch copy in 57.0 seconds. The uninstrumented
   final set also compiled successfully and the delivery dry run passed. The
   delivery tool's main-module re-elaboration with its automatic axiom probe
   timed out, so the exact compiled final modules are independently inspected
   using `#print axioms` in a scratch import file (compiled successfully in 1.8 s).
   `reindex_first_page_comparison` uses only `propext`, `Classical.choice`, and
   `Quot.sound`. Both `exists_etale_complex_abutment_presentations` and the new
   `exists_etale_complex_coherent_filtrations` use these three plus `sorryAx`,
   as expected from the one remaining split-off theorem. No other axioms occur.
3. **New statement — pass.** Read Stacks Tags [015J](https://stacks.math.columbia.edu/tag/015J),
   [015K](https://stacks.math.columbia.edu/tag/015K), and
   [0EZM](https://stacks.math.columbia.edu/tag/0EZM). The new theorem isolates
   functorial pages, finite categorical filtrations and their graded comparison;
   it does not assert continuity, invertibility of a comparison map, or the
   subgroup/quotient presentation being proved. In the flipped coordinates the
   outgoing target is `(p-q+1-r,q+r)` and incoming source is
   `(p-q+r-1,q-r)`: choosing `r > max(p-q+1,q-a)` kills both, uniformly in the
   stages. Exact inverse image and degreewise colimits preserve the lower bound.
   For `p<a`, derived cohomology vanishes, so the coincident top/bottom bounds
   at `a = max a (p+1)` are consistent. For a zero complex all pages and graded
   pieces are zero. For a complex concentrated in degree `a`, only filtration
   degree `a` contributes; for `q<a` or `q>p` the graded piece is zero. These
   checks include `p=a-1` and filtration length zero. No affine-transition,
   quasi-compactness, or geometric-limit hypothesis from 0EZM is used, because
   this interface only constructs comparisons and never asserts continuity.
   Independently searched LeanFinder with a bounded-below sheaf/finite-filtration
   query, Loogle for the cokernel projection API, Mathlib via msearch grep,
   `lean/Sheaf` for page and filtration interfaces, and the upstream spectral
   sequence/stupid-filtration modules. No existing theorem supplies the coherent
   diagram interface. `exists_etaleComplex_uniform_pages` fixes `q` before its
   existential diagram, and so cannot be used to obtain one diagram for all `q`.
   The new docstring has a full proof and its node matches the Lean statement.
   Closing this theorem is not a short missing algebraic calculation.
4. **Route and pruning — pass.** The main proof is a genuine reduction: it
   obtains categorical data, constructs a directed final reindexing with Mathlib,
   forms transported additive ranges, and proves kernel, surjectivity, membership
   and naturality by cokernel exactness and monicity. Local `have` proofs use the
   upstream cokernel API rather than add duplicate public helpers. Public imports
   serve signatures; added proof imports are plain `import`. The report now lists
   all six removed original proof imports and all seven replaced direct node
   dependencies, while distinguishing dependencies retained by the new node
   from global pruning. The unit `sk-prop-h2` has empty realized statement/step
   lists; no unit statement, step, or chapter route is bypassed or edited.
5. **DAG agreement — pass.** Read the original and delivered node records and the
   new node. Main-node steps describe exactly the implemented Mathlib reindexing,
   additive-range transport and cokernel argument; its dependency union is
   `def-sp-filtration` and the new coherent-filtrations node. The new node retains
   the spectral/convergence and functoriality plan and is assigned the original
   chapter/unit. Its creation, blueprint origin, source, searches and Lean record
   are present; the unavailable LeanSearch result is now explicitly marked
   unavailable. The new module now directly imports the available modules of
   its stated proof plan, without exposing these proof imports publicly.

Changes in this reading: corrected the incomplete pruning report, added the
new theorem's proof-plan imports, and marked its unavailable search explicitly.
No mathematical statement or proof construction was changed.

The previous return (2026-10-12 17:37 UTC) objected to duplicated private
`step_quotient_zero_iff` and `cokernel_map_apply` declarations. This delivery has
neither declaration: it proves the two short facts locally from Mathlib. The
original helpers are private and cannot be imported by name. The duplicate-name
and duplicate-statement checks passed in the final preflight.
