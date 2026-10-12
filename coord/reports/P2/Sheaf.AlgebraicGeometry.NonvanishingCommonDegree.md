## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_common_degree_nonvanishing` by constructing `M = L.tensorPow (p * q)` and both sections explicitly. Two proved private helpers convert evaluation-at-one sections to zero-locus complements and combine positive tensor powers with isomorphism transport. Added proof-only imports `Sheaf.AlgebraicGeometry.SectionNonvanishingZeroLocus` and `WeilConjectures.AlgebraicGeometry.Modules.AffineComplement`; removed the unused pullback-tensor import. The statement, universes, and existing docstrings are unchanged. Updated the node proof and dependencies to match this route.

The nonvanishing dictionary was initially absent from the compiled cache. Its unchanged repository source is copied into the sandbox only to compile that dependency locally; it is not an adaptation and contributes no diff to the delivery.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.Scheme.Modules.exists_common_degree_nonvanishing` (node `lem-weil-pbc-nonvanishing-common-degree`). Added zero holes. Neither the module nor the unchanged dictionary dependency contains `sorry`. The positive-power source lemma is already proved. The launcher compiler accepted both files without warnings; the dry run checks the axioms of all new declarations.

## No longer needed

Removed import `Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor` and proof dependency `lem-weil-pbc-invertible-pullback-tensor`. No pullback, fibre comparison, residue-field rank calculation, or finite tensor permutation from that module is used. Its own dependency tree is unnecessary for this theorem; other callers can still require it. Retained the statement import `Sheaf.AlgebraicGeometry.Ample` and added the dictionary and existing zero-locus power tools above. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG plan's fibre calculation is unnecessary: `compl_support_zeroLocus_tensorPowSection` in the source library already proves the positive-power locus identity. The newly available proved nonvanishing dictionary closes the gap noted in the node's earlier search. The route still constructs the common power and raises both sections, as the source prescribes. Zero sections, an empty scheme, and exponents one are covered without added hypotheses; positivity is used only in the two applications of the power-locus lemma.

Searches run: LeanFinder for positive tensor-power nonvanishing (structure-sheaf `basicOpen_pow` hits); Loogle for `tensorPowSection` (unknown identifier); Mathlib grep for `tensorPowSection|basicOpen_pow` (basic-open power identities); direct repository searches found the dictionary and the source power lemma, and the already proved finite-common-power-cover theorem using the same transport. No new statement or node is needed for these already proved tools.

## Second reading by P2

1. **No accidental visible changes.** Compared the delivered module and node with the repository versions. The theorem signature, universes, existing declarations, and docstrings are unchanged. The only module changes are proof-only imports, helper proofs, and the target proof; the node changes record the proof route and dependency pruning.

2. **Proof and axioms.** Compiled `SectionNonvanishingZeroLocus.lean` and `NonvanishingCommonDegree.lean` together with `lcompile.py --all`; both compiled without errors or warnings. The module has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The target proof constructs `L.tensorPow (p * q)`, transports both tensor-power sections through explicit isomorphisms, and applies the existing positive-power zero-locus theorem. The two private helpers are proved in full.

3. **Statements and dependencies.** The only target statement is unchanged and the module adds no public statement. The private helpers are strictly internal proof reductions, so no split-off theorem or node is needed. The retained statement import is `Sheaf.AlgebraicGeometry.Ample`; proof-only imports are `Sheaf.AlgebraicGeometry.SectionNonvanishingZeroLocus` and `WeilConjectures.AlgebraicGeometry.Modules.AffineComplement`. The old pullback-tensor proof dependency is unused. The old ample-invertible-module dependency is also removed from `proof_deps`; its definition remains in `stmt_deps` because it is part of the target's meaning.

4. **Shortest route and pruning.** The proof uses `nonvanishingLocus_eq_compl_support_zeroLocus`, `Hom.zeroLocus_eq_of_arrowIso`, and `compl_support_zeroLocus_tensorPowSection`; this avoids the former fibre and pullback calculation while preserving the common-degree construction. No shorter existing declaration was found by repository search or the recorded Mathlib searches. The unit route and its realized statements are unchanged.

5. **Node agreement.** The node's proof steps, `proof_deps`, and `proof_origin` match the Lean proof and its imports. No new nodes or change records are introduced.

Changed in this second reading: none to the Lean proof; this report section records the dependency and statement checks.
