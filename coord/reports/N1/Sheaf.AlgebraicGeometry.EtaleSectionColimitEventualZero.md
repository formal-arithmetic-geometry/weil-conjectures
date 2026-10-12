## What changed

Added `EtaleSectionColimitEventualZeroAux` with two strictly intermediate theorems: extraction of finite local zero-cover data and the finite-cover filtered equalization step. The target theorem now combines these two statements by a real Lean proof. The target module imports the auxiliary module.

## Proved and sorry left

`AlgebraicGeometry.etale_section_colimit_eventual_zero` is proved from the two intermediate statements. The auxiliary declarations `etale_section_colimit_finite_zero_cover` and `etale_section_colimit_eventual_zero_of_finite_cover` remain `sorry`, with nodes `lem-weil-pbc-etale-section-colimit-finite-zero-cover` and `lem-weil-pbc-etale-section-colimit-eventual-zero-finite-cover`.

## No longer needed

No stated proof dependency imports were removed; the original module contained only Mathlib imports and the proof is reduced through the new auxiliary module.

## Where the brief, the DAG or earlier work was wrong

The full Stacks argument is substantially longer than a direct local proof in Lean. It was split into the two substantive intermediate steps above; no statement was weakened.

## New nodes

`lem-weil-pbc-etale-section-colimit-finite-zero-cover` and `lem-weil-pbc-etale-section-colimit-eventual-zero-finite-cover` are stated in `EtaleSectionColimitEventualZeroAux` and correspond respectively to the local finite-cover extraction and finite filtered equalization parts of Tag 0738.

## Earlier second reading (a previous round; superseded)

The target signature is unchanged and its proof is a genuine application of two strictly
smaller intermediate statements. The new statements match the finite-cover extraction and
filtered equalization steps of the cited Stacks proof.

## Second reading by N1

1. **Visible changes and statements.** Compared both delivered modules against the repository module. The target theorem signature is byte-for-byte unchanged. The auxiliary module adds only the two named split-off declarations; no existing declaration was altered. The target's new auxiliary import is proof-only (`import`), while the public imports remain those required by its signature.

2. **Proof checks.** Both modules compile with `lcompile.py --all`. There are no `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations, and no `sorry` occurs in a definition. The target proof is a genuine application of the two intermediate theorems. A scratch `#print axioms` check reports only the permitted axioms together with `sorryAx` from the two explicitly split-off theorems.

3. **Split-off statements.** The two remaining `sorry`s are named public theorems with source citations, complete proof sketches in their docstrings, and matching DAG nodes. Their hypotheses are strictly intermediate: the finite-family theorem records local eventual vanishing plus the separatedness implication, and the extraction theorem records finite local data from a zero colimit section. Searches found no existing Mathlib or library declarations duplicating them. The finite-family node wording was corrected to match its Lean hypothesis (the separatedness implication carries the covering consequence).

4. **Pruning and route.** The target follows the delivered finite-data then finite-filtered-equalization route. No stated proof dependency or import became unused, so there is no pruning to report. The unit route and `realized` data are unchanged.

5. **DAG agreement.** The target node's proof and `proof_deps` name exactly the two auxiliary declarations. Each new node's Lean record, source, proof origin, chapter, and unit agree with the corresponding declaration and module.

Changed in this second reading: clarified the finite-family auxiliary docstring and synchronized its DAG statement with the actual Lean signature. No mathematical statement was weakened.
