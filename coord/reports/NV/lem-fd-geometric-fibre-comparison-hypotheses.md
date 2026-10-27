## Worker report

Files written:

- `dag/nodes/sec-fourier-transform/lem-fd-geometric-fibre-comparison-hypotheses.json`: statement, split into five proof steps; not a Mathlib leaf. Statement and statement dependencies preserved.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log.

## New nodes

None. There are zero new nodes and zero new Mathlib leaves. The existing general results already state all non-elementary ingredients. In particular, creating new geometric-fibre Noetherianity, finite-dimensionality, or Frobenius-inverse nodes would duplicate existing results or merely repackage clauses of the item.

## Attachments

None. Searching the project `lean/WeilConjectures/` for the exact blueprint tag found no declaration. Concept searches located `AlgebraicGeometry.WeilSheaf.isLocallyNoetherian_geometricFiber` in `WeilConjectures/WeilSheaf/Category.lean:193` and `topologicalKrullDim_geometricFiber` in `WeilConjectures/WeilSheaf/CompactSupportAdicConstant.lean:251`. I read both: the former proves only local Noetherianity; the latter equates two dimensions without proving a finite global bound. Neither states every clause, so neither is an attachment of this item.

## Literature and searches

WANTED: none.

I read the current `sec-fourier-transform/sk-def-trace/def-fd-trace-function.md`, its unit record `sk-def-trace`, and its chapter record. The ancestor is `def-fd-trace-function`, whose final coefficient-category reference motivates this auxiliary admissibility check; this auxiliary has no independent imported proof. The proof is recorded as agent assembly of the existing mathematical statements, rather than attributed to a nonexistent detailed blueprint proof.

I read Stacks `schemes.tex`, `lemma-separated-permanence`, Tag 01KU, specifically item (3); `morphisms.tex`, `lemma-base-change-finite-type`, Tag 01T4, and `lemma-finite-type-noetherian`, Tag 01T6. I checked those tags in `stacks-project/tags/tags`. I read the current blueprint statement `lem-kun-dimension-finite-type`, which says finite type over any field implies finite dimension. I read Deligne, Weil II (1.1.7), printed pp. 150–151, from PDF pages 15–16: arithmetic Frobenius is the power automorphism and geometric Frobenius its inverse. The scheme action is the induced action on the second factor, as in (1.1.10)(i) on p. 151 and the existing Frobenius-square node.

Whole-DAG searches by dimension, Noetherianity, base-change and Frobenius concepts found the existing nodes used below. Whole-blueprint searches included `finite type dimension`, `separated finite type base change`, `kundim`, `Frobenius`, `Noetherian`, `geometric-fibre admissibility`, and `finite type over`. The dimension search specifically found `lem-kun-dimension-finite-type` and `def-kun-dimension`; no imported node states the complete conjunction of the item, so `same_as` remains empty. The original item's Mathlib searches were retained as historical records. New LeanFinder, Loogle, LeanSearch and grep queries were run through `msearch.py`; their actual results are appended exactly and recorded in `searches.jsonl`. A second LeanFinder phrasing addressed base change and Frobenius. The hits concern Noetherianity predicates, local Noetherianity, base-change instances and the field Frobenius; none proves the complete conjunction in one specialization. I read the Noetherian class and relevant instances in Mathlib's `AlgebraicGeometry/Noetherian.lean` at 239–242, 280–281 and 342–347. No new leaf is claimed.

## Issues and unfinished work

No error in the item's mathematical statement was found, and no statement correction was made. Its imported proof was empty; this delivery supplies the argument. No Lean was written and no compiler, Lake or build command was run. All non-elementary facts have existing nodes. No mathematical part remains unfinished at stage 1; the cited unsplit dependencies remain their own items.

## Not duplicates

No new-node/existing-node pairs arise because no new nodes are created. I reused `lem-pod-separated-finite-type-base-change`, `lem-weil-pbc-finite-type-over-noetherian`, `lem-kun-dimension-finite-type`, and `lem-weil-frobenius-square-cartesian` instead of creating their geometric-fibre special cases.

## Review by NV

I checked the item against the actual source setting: it starts with a separated finite-type scheme over the finite field, and the new geometric fibre is formed over its fixed algebraic closure. No step assumes that this infinite algebraic extension is finite. The statement is self-contained through its unchanged six definition dependencies and explicit Noetherian and empty-dimension conventions. There are no new statements to test or sources to certify. I checked the five steps as follows, with every cited node's statement open.

1. `def-weil-finite-field-fiber` explicitly identifies the geometric fibre and its structure map with this base change. `lem-pod-separated-finite-type-base-change` explicitly allows any base morphism and concludes both separatedness and finite type. This is exactly what step 1 takes; no assertion is inferred from a definition of finite type alone.
2. `def-weil-pbc-noetherian-ring` defines finite generation of every ideal, and `pqf-def-locnoeth` gives the affine-cover definition. The two ideals of a field and the single point of its spectrum establish the Noetherian target directly. `lem-weil-pbc-finite-type-over-noetherian` explicitly concludes Noetherianity of the source from a finite-type morphism and a Noetherian target. Both hypotheses now hold; I checked that the conclusion includes quasi-compactness, so local Noetherianity alone is not silently substituted.
3. `lem-kun-dimension-finite-type` says exactly that every finite-type scheme over a field has finite global dimension. It requires neither properness, smoothness, nonemptiness nor algebraic closedness. `def-kun-dimension` defines this by strict irreducible-closed chains. The remaining passage to a natural bound is just bounding a finite supremum of integer lengths. The empty case uses the item's explicit minus-infinity convention and takes bound zero. This is a tool use of a dimension theorem from another unit, recorded in `split_report.tool_uses`; it does not replace the trace unit's route.
4. `def-weil-finite-field-q-elements` explicitly states characteristic p; `def-weil-finite-field-fiber` supplies the field extension. Bezout for two distinct primes writes the inverse already in the prime subfield. Applying a unital ring map to the displayed product proves the claimed inverse in each stalk. This step is elementary, with its actual calculation given. I tested the point case and the empty case: at a point the inverse is the field inverse; on the empty scheme the assertion is vacuous. In particular no unstated theorem about preservation of units is hidden here.
5. Clause (1) of `lem-weil-frobenius-square-cartesian` explicitly states both isomorphism and inverse for arbitrary model schemes. `def-weil-frobenius-detailed` explicitly identifies the inverse field automorphism with arithmetic Frobenius. The composites are written out on both factors, so the semilinear map is never mistaken for a k-linear automorphism. The projection case X_0 = Spec(k_0) gives Spec(gamma) with inverse Spec(varphi_q); the empty case gives the unique identity. This generic Frobenius theorem is also declared as a tool use.

I also tested an affine line and a nonreduced affine finite-type model: none of the proof uses reducedness or equidimensionality, and the base-change theorem and global dimension theorem still apply. Taking ell=p would destroy the stalk-unit conclusion on Spec(k), so the given prime inequality is essential and is used exactly in step 4. All steps are shorter than 2000 characters. Each non-elementary step cites the theorem that states its conclusion, not a definition or the internal proof of another node. The statement quotations in `citations.json` are copied verbatim from those opened nodes. No SGA route or source is used. B1–B9 are either satisfied by the preserved item or inapplicable because there are no new nodes; C1–C5 and D1–D5 were checked through the explicit steps above; the hypotheses, objects, composite maps and edge cases of E were checked as described. No correction beyond supplying the missing proof was needed.
