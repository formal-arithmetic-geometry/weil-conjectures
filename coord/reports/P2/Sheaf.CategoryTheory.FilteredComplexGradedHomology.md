## What changed

Proved `CategoryTheory.filteredComplex_graded_homology` in
`Sheaf.CategoryTheory.FilteredComplexGradedHomology`, preserving its signature and visibility.
Added the proof-only import
`Sheaf.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries` for its existing cycle and
boundary identifications. A proved private helper `CategoryTheory.homology_quotient` derives
the image-in-kernel cokernel description from Mathlib's kernel-lift homology description,
`cokernel.mapIso`, and `cokernelEpiComp`. The main proof constructs the short-complex
isomorphism explicitly from `e` and `hd`, transports it through homology, and composes.
Updated the existing node's proof, proof dependencies, and proof origin to match this route.
All public imports are unchanged.

## Proved and sorry left

Closed the sole original hole: `CategoryTheory.filteredComplex_graded_homology`
(node `lem-sp-filtered-complex-graded-homology`). The private helper
`CategoryTheory.homology_quotient` is also fully proved. No sorry remains in the item;
no holes or modules were added. This proof uses the existing theorem
`CategoryTheory.DecreasingFiltration.filteredComplex_firstPage_cycles_boundaries`
(node `lem-sp-filtered-complex-first-page-cycles-boundaries`), which still has a sorry
in the repository. That dependency is not claimed to be proved by this delivery.

Local single-file compilation passed without warnings. The delivery dry run performs the
final compiler and preflight checks.

## No longer needed

Removed the redundant direct proof-only import `Sheaf.CategoryTheory.Filtration`; its
public definitions remain available through `FilteredComplexSubquotients` and are still
needed by the statement. No mathematical dependency nodes or reachable modules are pruned:
`def-sp-abelian`, `def-sp-filtration`, and `def-sp-filtered-complex-subquotients` remain needed.
The existing first-page cycles-boundaries lemma provides the filtration calculation,
so no duplicate calculation theorem or new node is needed. An explicit Mathlib
`ImageToKernel` import tested during development was unnecessary and is absent from the
delivery; the API is already imported transitively.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original DAG listed only definition nodes for the
non-elementary filtration calculation; the existing first-page cycles-boundaries node
already supplies precisely that calculation without any finiteness hypothesis or import
cycle. The revised DAG records its use. The unit record has no realized statement or step
nodes at this item, and no unit route is bypassed.

## Second reading by P2

1. Compared the delivered module with the repository version. The public theorem signature and all existing declarations are byte-for-byte unchanged; only the proof-only import, private helper, and proof body differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. The proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The helper and target use only ordinary Mathlib/library results; no hollow definition was introduced. Verdict: pass.
3. The only nontrivial route uses the existing `filteredComplex_firstPage_cycles_boundaries` theorem and a private quotient reduction. The quotient helper is a genuine reduction to Mathlib's kernel/image API, and no duplicate public statement or unnecessary split-off node was added. Verdict: pass.
4. The proof follows the target downward, keeps the first-page filtration calculation route, and removes the redundant direct `Filtration` proof import. Verdict: pass.
5. The DAG proof, proof dependencies, and proof origin now match the Lean proof, including the first-page cycles/boundaries node. The unit record has no realized steps at this item, so no unit route is bypassed. Verdict: pass.

Changed after review: no proof or statement changes were needed; this section records the checks above.
