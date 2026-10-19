# Q66: lem-trf-valuation-finite-height-composition

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-valuation-finite-height-composition.json`: statement, split into six elementary steps, no Mathlib match for the full statement.
- `citations.json`: one entry for every step/node citation, quoting the existing statements verbatim.
- `report.md`: this report and self-review.

## New nodes

None. Zero new nodes and zero new Mathlib leaves. The two existing definition dependencies are already Mathlib leaves.

## Attachments

None. Searched the slopmaster2 project under `WeilConjectures/` for the exact blueprint tag and item id, valuation/finite-height/composition, integral closure, and valuation/quotient combinations. No declaration gives the item. The valuation-composition material in `WeilConjectures/Mathlib/RingTheory/Valuation/ValuationSubring.lean` concerns composition of valuation rings, not this algebra residue comparison. The isolated upstream master is reference material only; its search also found no declaration for this item. The item has no existing Lean audit entry to repair.

## WANTED

WANTED: `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, Theorem 3.5.5, Step 4, printed pp. 23–24, for lem-trf-valuation-finite-height-composition. The primary PDF was read online at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf (arXiv:0707.3953v3, 14 April 2010); the named local archival copy is absent. No literature was downloaded or written. The elementary expansion is marked `proof_origin.by = agent` to respect the missing-local-document rule.

## What was wrong or changed

The item statement is correct and was retained byte for byte. Its name reflects its application to finite-height induction, but its statement correctly makes no height assumption. The imported node was statement-only. The new proof spells out the prime-ideal divisibility that Temkin uses, the equality of ideals as subsets of the localization, both quotient kernels, and both directions of the residue integral-closure claim. Instead of invoking a generic theorem that normalization commutes with arbitrary quotient, the converse uses the actual monic equation and the proved ideal equality. No such generic quotient theorem is assumed.

The current `main-20261015` ancestor and the unit `sk-i-curve-zero` use contracting correspondences, while this node belongs to the already recorded historical normalization chain. I read the current ancestor update and the unit/chapter records, retained that provenance exactly, and made no change to any unit route or binding. The parent `lem-trf-valuation-reduced-fibre-normalization`, step 8, applies exactly this statement after arranging relative integral closedness of its T-localization.

## Searches and reuse

At startup the sandbox held only four brief markers: no prior item, report, citations, or search results. I used the current repository item as the starting copy. The repository had Q82's earlier Mathlib search record; I retained its query history, ran those exact queries for Q66, read their current results, and updated the results to the actual Q66 hits. `searches.jsonl` is the search command's own log and was not edited.

Two semantic phrasings (LeanFinder), the Loogle query, a full-Mathlib integralClosure/quotient grep and LeanSearch found no exact theorem or one-line specialization. The second grep, `quotient_isIntegralElem|theorem.*quotient|lemma.*quotient` in `RingTheory/IntegralClosure`, identifies monic polynomial quotient integrality and forward passage of integrality to quotients; neither supplies this inverse lifting claim or the valuation ideal equalities. All six executed queries are recorded exactly with the tools and query text actually used.

Searched the entire DAG by valuation, integral-closure, residue/quotient and localization concepts, and the whole imported blueprint using `tools/blueprint_refs.py search` for `relative integral closure valuation prime`, `integral closure`, `valuation`, and `integrally closed in`. The blueprint results give general valuation/normality definitions and other unrelated coefficient constructions, not another statement of this comparison. The ancestor command confirms `lem-trf-local-term-locality`.

## Not duplicates

No new nodes, so there are no new/existing-node pairs to distinguish. The divisibility of the prime under T and the monic-equation adjustment are short proof steps, not separate lemma nodes or restatements of the item as children.

## Review by Q66

I read Temkin Theorem 3.5.5 Step 4 across printed pp. 23–24 from the primary PDF. Its argument first replaces A so its T-localization equals its relative normalization; it then uses T-divisibility of the valuation prime, identifies the residue embeddings, and lifts a residue integral equation. I checked this proof at the stated generality rather than importing the finite-type or separably-closed assumptions of the surrounding theorem. I also read the existing statements of `def-trf-valuation-ring` and `def-weil-pbc-integral-closure` in full, and the local Stacks text at Tags 00I9/00IB and 00GI/00GO/00GP (the valuation-ring characterization and monic-equation/subring descriptions).

Step 1 cites only the valuation definition, whose statement explicitly gives the element-or-inverse dichotomy. Applied to q/t with q and t nonzero it rules out t/q by membership in the prime; the remaining use of primality establishes q/t in the prime. The zero q case is explicit, and the zero algebra is disposed of before any degree argument.

Step 2 cites no new theorem: it uses step 1 term by term in the finite-sum definition of the extended ideal. A is already viewed inside its generic fibre by hypothesis, and every denominator in T is nonzero, so the displayed fractions describe the specified localization inside that generic fibre. It proves the ideal equality before treating pA as an ideal of A_T.

Step 3 cites the integral-closure definition. This node explicitly says both that integral elements form a subring containing the base and that integrality is a monic equation. Re-reading that equation over A_T and using the item's actual relative integral-closedness hypothesis proves B is contained in A_T. The equalities of pA, pB, pA_T then follow by a sandwich, not by a finiteness theorem.

Step 4 cites no node: the quotient injections are calculated from their exact kernels, using the equal ideal already contained in A. No faithful flatness or finiteness assumption is silently used.

Step 5 cites the integral-closure definition for the monic equation and its meaning after quotient. Reducing every coefficient and the equation directly proves integrality of the embedded residue of each b.

Step 6 cites that same definition, whose statement also gives exactly the reverse membership criterion. For any integral residue, quotient surjectivity gives a lift z and coefficient lifts. The evaluated error e lies in pA by step 2, so subtracting e from the constant coefficient gives an actual monic equation over A. This supplies the missing inverse direction without claiming that normalization commutes with arbitrary quotient or appealing to a theorem about normal domains. A need not be a domain or reduced. The degree is positive, as required by the cited definition.

Hypothesis and small-case checks: the only use of valuation is step 1, the only use of the relative-normality assumption is B contained in A_T, and torsion-freeness justifies the given ambient inclusion. For A=0 everything is zero. For p maximal, T consists of units, so A_T=A and the assumption immediately forces B=A, consistent with the proof. For A=K, pA=A (p is nonzero) and both residues are zero. The same is true on any component where an element of p is inverted. For A=V the assertions specialize to pV_p=p and the valuation residue comparison. A ring with nilpotents is not excluded: the argument only requires the stated relative integral closedness and monic equations. No finite height, finite generation, separable closedness, perfection, minimality of p, or properness of pA was introduced.

I checked delivery-errors B1–B10, C1–C8, D1–D5 and E1–E7 against the actual files: there are no new nodes needing statements/searches/blueprint tags, the item statement is self-contained as before, all its cited nodes say exactly what is used, and every other step is the written elementary argument. There is no source error or statement dispute, relabelled child, non-elementary hidden lemma, off-unit theorem, or circular citation. The subring assertion is explicitly included in the existing Mathlib-backed integral-closure definition; it is not inferred from a definition that lacks it. All steps are below 2000 characters. `proof_deps` equals the union of `uses`, and citations.json quotes the actual current statements. I wrote only inside this sandbox, ran no git command in the shared repository, and wrote no Lean or compilation/build command.

## What could not be finished

Nothing mathematical remains for this one-level split. The archival PDF remains WANTED. Delivery preflight results are recorded below after running the required server checks.

## Validation

The required `deliver.py Q66 lem-trf-valuation-finite-height-composition --no-push` exited successfully: `OK (not pushed)` at candidate `7d4b6e56dc`, server preflight passed. I separately verified that the delivered statement equals the shared statement exactly, the six step lengths are 537, 488, 432, 298, 281 and 604 characters, and all four entries of citations.json are verbatim substrings of the cited current statements. No local DAG/preflight checker or compiler was run.
