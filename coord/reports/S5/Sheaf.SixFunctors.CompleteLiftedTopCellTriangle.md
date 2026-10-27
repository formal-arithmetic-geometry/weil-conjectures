## What changed

Proved `WeilConjectures.CompleteLiftedTopCell.complete_lifted_top_cell_triangle` in `Sheaf.SixFunctors.CompleteLiftedTopCellTriangle`, retaining its entire signature, including independent universes, the prescribed normalization, terminal-section surjectivity, and rank zero. All added helpers are private and proved. The proof obtains top epimorphy from strict quotient triangles and complete-tower bounds, lifts via projective homology, checks the exact scalar-extension-unit square, and proves cone completeness using local principal-localization tests. Updated the node's proof, dependencies, proof origin, and obsolete tool-use entries.

Four definitions replace explicit `letI` bindings with `let` to avoid repeated inlining. Both forms register identical values, and zeta reduction makes the definitions definitionally equal. The two `HasDerivedCategory.standard` values in `residueTorTest` carry localization data; their equality does not rely on proof irrelevance. Local priority for the canonical scalar-reduction derived-category instances also avoids repeated unfolding of competing standard localizations. The Roos/intrinsic equivalence and sliced integral operations use ordinary private imports, and a good K-flat representative is constructed through the public resolution API. No other module changes. The change record is `coord/changes/S5-complete-lifted-top-cell-proof-instances.md`; consumer checks find no downstream modules.

Validation: the full assigned module compiled without warnings in 53.8 seconds. An exact copy with the delivery axiom probe also compiled in 58.1 seconds; its scan took 402 milliseconds and reported no forbidden axiom. All component proofs were also compiled during development. The empty-product case is proved directly, and neither strict inequality of the interval nor nonemptiness of the scheme is introduced.

## Proved and sorry left

Closed 1 of 1 original holes: `WeilConjectures.CompleteLiftedTopCell.complete_lifted_top_cell_triangle` (node `lem-sf-complete-lifted-top-cell-triangle`). Added 0 holes; split off 0 statements; 0 sorries remain in the delivered Lean file. This is a proof from existing library declarations, including declarations that remain assigned to other workers; it is not a claim that the entire transitive axiom closure is already finished.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`: coefficient identifications already occur in the completed free-resolution API.
- `Sheaf.Paper.CompleteResidueCohomologyBounds`: its theorem identifies the coefficient and scheme universes. The proof here supplies the independent-universe bounds directly from strict DVR triangles and the bounded epimorphic derived-limit theorem.
- `Sheaf.Algebra.Homology.RegularQuotientFlatSequence` and `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`: the canonical reduction triangle is already a clause of the completed free-resolution theorem.
- `Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison`: ordinary adjunction normalization, the free K-flat counit, and generic single-complex comparisons give the exact quotient square.
- `Sheaf.Paper.ConstantCompletionEquivalence` and `Sheaf.CategoryTheory.RingedCompleteTriangulated`: use the existing unit-compatible Roos/intrinsic equivalence and exact internal-Hom local tests instead.

Accordingly removed direct proof-dependency edges to `det-prop-sfb-qlbar-colimit-x-integral-limit`, `lem-sp-completed-coefficient-regular-quotients`, `lem-sf-complete-residue-cohomology-bounds`, `lem-cbc-regular-quotient-flat-sequence`, `lem-weil-pbc-complex-ses-triangle`, `lem-sf-ringed-kflat-single-tensor-comparison`, `lem-weil-pbc-constant-completion-equivalence`, and `lem-sfb-ringed-complete-triangulated`. Removed the corresponding obsolete tool-use entries, preserving the order of retained entries. `def-weil-abstract-derived-category` remains a statement dependency, so its redundant direct proof edge is unnecessary.

No module is withdrawn. These removals concern this proof's direct route; dependencies still used by imported declarations remain needed, and no source-library declaration is removed. The blueprint unit has no fixed realized statement or proof-step nodes, and the top-cell construction and complete-cone argument of its route are preserved.

## Where the brief, the DAG or earlier work was wrong

The cohomological-bounds declaration uses one universe for the scheme and coefficient field, whereas this item's statement deliberately separates them. Its mathematical proof extends: test the independent-universe Tor predicate with the unit on the terminal slice, propagate bounds through the strict DVR quotient triangles, and apply the independent-universe bounded epimorphic derived-limit theorem. The public statement required no repair. Competing derived-category instances and inlined exactness proofs made elaboration expensive; the local instance priority and explicit let bindings keep the whole proof within the compile limit.

The initial DAG prescribed rebuilding a regular-quotient complex triangle, although the existing completed free-resolution theorem already provides the needed canonical reduction triangle. Likewise, generic exactness of the local internal-Hom tests suffices for the complete cone; the broader constant-completion and triangulated-completeness interfaces are unnecessary here. No disputed statement or new unproved result was introduced.


Repair of returned head `4b91f1a81b9` (reviewer `C-4b91f`): the proof was accepted, but landing rejected the reviewer override filename. The change record is delivered at `coord/changes/S5-complete-lifted-top-cell-proof-instances.md`. `tools/batch_land.py` maps that record to the override alias `S5-complete-lifted-top-cell-proof-instances.change.md`, not `S5-complete-lifted-top-cell-proof-instances.md`. This packet incorporates the corrected instance explanation directly in the delivered record, so no override is needed for it. It also records the correct alias if the reviewer supplies further changes. The mathematical proof and route remain those reviewed at the returned head. In addition to a comment explaining the local instance priority, the repair replaces two local partial applications of generic lemmas with direct applications and supplies their canonical instances explicitly. This avoids rechecking large intermediate function types. The source was compared with the current `sheaf-dag` module, and the repaired module compiled on the server without warnings in 44.3 seconds before resubmission. The delivery tool rebases the packet on the freshly fetched `origin/sheaf-dag`.

The repair dry run passed compilation and server preflight on freshly fetched `sheaf-dag` (dry-run commit `9e96fc496cd`). A separate server-compiled check proves equality with each original definition by `rfl`: `freeQuotient`, `freeCellQuotient`, `topReduction`, and `residueTorTest`. The auxiliary check has no holes and is outside the delivery.

The final delivery attempt exceeded the compile limit despite the earlier passing dry run. Diagnostic server compiles isolated the cost in generic-lemma specialization. Direct applications of `derived_single_normalization` and `projective_normalized_lift`, with explicit canonical instances, make the complete module compile without warnings in 48.6 seconds. No signature, definition, dependency, or mathematical argument changes in this additional proof-only adjustment.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
