# Stage-1 report: def-sfb-symmetric-bimod-module-iso

## Files written

- `dag/nodes/sec-proetale-coefficients/def-sfb-symmetric-bimod-module-iso.json`: existing definition, now split into its complete one-step proof; statement and dependency are unchanged; no Mathlib exact match; no new nodes.
- `citations.json`: exact quotation for the existing lemma used by step 1.
- `report.md`: worker report and independent review.

## Attachments

None. Searching `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item id, `Bimod.IsSymmetric.iso`, and the relevant symmetric-bimodule terms found no declaration. The archived upstream-master source contains `CategoryTheory.Bimod.IsSymmetric.iso`, but it is outside the permitted slopmaster2 attachment source and is not a finished declaration in the source checkout used for this split.

## WANTED:

None. The blueprint proof paragraph supplies the argument, and no external literature is required.

## What was wrong in the node, blueprint, or brief

The imported node was structurally unsplit (`status: imported`) and had no Mathlib searches. Its statement and proof agree with `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-prop-sfb-module-category/def-sfb-symmetric-bimod-module-iso.md` and the corresponding `.proof.md`; I changed only the worker-owned split fields, set `status` to `split`, recorded the required searches, and filled `blueprint.same_as` with the empty search result. No statement correction was needed. No additional node is justified: the sole proof step is the direct identity-map construction from the existing symmetric-bimodule lemma.

## Review by Q26

I read the item node, its blueprint statement and proof, the neighbouring proposition proof, and the existing node `lem-sfb-modobj-symmetric-bimodules`. I also searched the whole blueprint with `tools/blueprint_refs.py search` and searched the read-only slopmaster2 source for the exact item id, `Bimod.IsSymmetric.iso`, `IsSymmetric`, and bimodule/module-object terms. The source checkout has no declaration for this item, while Mathlib has only generic `Bimod.isoOfIso` and identity/action infrastructure; the eight recorded `msearch.py` calls cover LeanFinder, Loogle, grep, and LeanSearch with two phrasings each where applicable.

Step 1 was checked against the cited node verbatim. That node states the attached right action as `\\rho_M := \\gamma_M \\circ \\beta_{M,\\mathcal R}` and defines symmetric bimodules by the right-action/braiding equality. Specializing its module object to the left-action module underlying `P`, the attached bimodule has the same underlying object and left action as `P`; the symmetry hypothesis identifies its right action with `P`'s `\\rho_P`. Therefore the identity underlying map satisfies both `Bimod.Hom` action compatibilities, and `Bimod.isoOfIso` with the identity object isomorphism gives the claimed bimodule isomorphism. I checked the same argument in the archived master implementation only as mathematical reference; I did not attach it because the brief restricts attachments to slopmaster2 and the declaration is not present there.

I tested edge cases conceptually: the identity object map remains an isomorphism when the underlying object is initial or terminal, and no coequalizer or extra exactness hypothesis is used. The item introduces all of its objects and keeps exactly the braided-category, commutative-monoid, and symmetric-bimodule hypotheses. There are no new nodes, no duplicate pairs, no unresolved citations, and no SGA sources.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.


## Earlier second reading (a previous round; superseded)

- Item statement: checked word for word against main-20261015 `sk-prop-sfb-module-category/def-sfb-symmetric-bimod-module-iso.md` and against the hypotheses of its cited lemma. Verdict: correct for a braided monoidal category, a commutative monoid object, and a symmetric bimodule; no coequalizers, exactness, or symmetric braiding are needed.
- Step 1: opened the full statement of `lem-sfb-modobj-symmetric-bimodules` and its cited module-object definition `sk-def-sfb-module-objects`, and read the item's `.proof.md`. The lemma gives precisely the construction and right-action formula used; the symmetry hypothesis gives equality with the original right action. Verdict: supported, with the inverse construction and the two inverse equations now explicit. The calculation is elementary after the cited input, and uses neither the proof nor the full-faithfulness clause of that lemma.
- New nodes: none. Verdict: no elementary child, duplicate, special case, clause restatement, or potential new Mathlib leaf to remove; B1–B7 are vacuous for new nodes. The existing dependency is strictly the prior module-to-bimodule construction, not a restatement of this item's reconstruction of a supplied symmetric bimodule.
- Source and edge cases: compared with the unit `_section.md` relative-tensor clause and the archived master `Bimod.IsSymmetric.iso` (reference only). Checked vector spaces over a field with a commutative algebra and a module, including the zero module and the rank-one regular module: the maps and both inverse composites are identities. For the zero coefficient ring only the zero module occurs; for sheaves on the empty scheme the unique object and identity maps give the same result. No positive integer parameter occurs, so n=0 or n=1 imposes no additional condition. Verdict: no statement dispute or route change.
- Independent search: ran LeanFinder with “symmetric bimodule identity isomorphism attached module object” and a valid Loogle query `Bimod.isoOfIso` (three generic constructor/projection hits), plus grep with `isoOfIso|IsSymmetric` in Mathlib's `CategoryTheory/Monoidal/Bimod.lean`, recording actual outputs in searches.jsonl. Read Mathlib lines 107–166: `Hom` has the two action equations, composition is underlying composition, and `isoOfIso` at line 148 only packages an underlying isomorphism after those equations have been supplied. It does not define the symmetric-bimodule/module construction, so it is not an exact leaf for this item. Directly searched the read-only slopmaster2 project for the item and symmetric reconstruction names; no matching declaration exists. Verdict: retain the elementary split and no attachment.

Changes and reasons:

- Expanded the one step to give identity morphisms in both directions and their composites, completing the isomorphism rather than leaving the inverse implicit (C2/E5).
- Marked that step elementary because it now reduces explicitly to two reflexive action equations and identity composition.
- Corrected proof_origin to the actual `.proof.md` file, which contains the paragraph; the statement source stays unchanged.
- Corrected the two unsuccessful Loogle query verdicts to record identifier/parser failure rather than evidence of absence, and added the independent searches with their actual outcomes.
- Kept the original worker review and the verbatim citation unchanged; its quoted statement is still exactly what the repaired step uses. No statement, hypothesis, dependency, or node inventory changed.

Validation: the required delivery wrapper dry run printed `OK (not pushed)` at `782ebab81b`; preflight passed. The wrapper accepts group, item, and `--no-push`, so its supported invocation omits the literal trailing dot from the brief. No compiler, Lake, or Lean-writing tool was run.

Delivery attempt after the successful dry run: preflight stopped before push because the latest base contains an unrelated malformed `sec-smooth-purity/def-cbc-enhanced-diagrams-cones.json` (Extra data at line 187, column 2). This file is outside the item and was not edited. Retrying the supported wrapper against the latest base.

Retry result: `OK (not pushed)` at `d85ea92977`; preflight passed after the unrelated base-file problem cleared. Proceeding with the normal delivery wrapper.

## Second reading by Q26

- Item statement: read main-20261015 `sk-prop-sfb-module-category/def-sfb-symmetric-bimod-module-iso.md`, its separate `.proof.md`, the neighbouring lemma's statement source, and the proposition's relative-tensor clause. Every hypothesis agrees: braided monoidal category, commutative monoid object, and a symmetric bimodule. The module is obtained by forgetting its right action, and the isomorphism has direction from the reconstructed bimodule to the original one. Verdict: exact source statement; no statement dispute. This source is the blueprint, not a Stacks tag, so there is no Stacks-tag attribution to check.
- Step 1: opened `lem-sfb-modobj-symmetric-bimodules` and `sk-def-sfb-module-objects`. The former's statement, without using its proof or full-faithfulness assertion, constructs the bimodule with unchanged object and left action and right action gamma composed with beta. The hypothesis on P identifies that right action with rho_P. The latter defines the underlying left module and its morphisms. Read Mathlib `CategoryTheory/Monoidal/Bimod.lean:107–164`: bimodule morphisms have precisely the two action equations; their composition and equality are determined by the underlying maps. Thus in each direction the identity satisfies both equations by functoriality of tensor, and the two composites are identities. Verdict: the single step proves the entire conclusion by an elementary calculation; C1–C4 and E1/E5 pass. No nontrivial fact has been hidden under “transports” or “similarly”.
- New nodes: none. Verdict: B1–B7 are vacuous for new nodes; no elementary child, duplicate, clause restatement, or new Mathlib leaf is warranted. Searched the whole blueprint using `tools/blueprint_refs.py search 'symmetric bimodule'` and the DAG using the symmetric/bimodule keywords. The four matching blueprint nodes distinguish module-to-bimodule construction, this reconstruction, relative tensor product, and closure under tensor; none makes a new child necessary.
- Independent Mathlib and source audit: ran fresh positional `msearch.py` LeanFinder, Loogle, and grep calls, whose actual outputs are in `searches.jsonl`. LeanFinder's new phrasing returned unitors, regular bimodules, and an algebra/module equivalence ingredient. Loogle returned the three generic `Bimod.isoOfIso` declarations. Grep found `isoOfIso` at lines 148, 747, 756, and 765 and no `IsSymmetric`. Read the constructor and action equations directly: the constructor requires action compatibilities and supplies no module-to-bimodule construction, so it is not an exact declaration of this item. Direct searches of read-only slopmaster2 for the item, `IsSymmetric`, `fullyFaithfulToBimod`, and `toBimodObj` found no attachment. The archived master at `WeilConjectures/CategoryTheory/ModuleObjects/Bimod.lean:172` is mathematical reference only. Verdict: keep the elementary proof and no attachment or Mathlib leaf.
- Edge cases: in vector spaces over a field, for both the zero module and the rank-one regular module over a commutative algebra, the forward map, inverse map, and their composites are identities. With zero coefficients or sheaves on the empty scheme the same identity calculation applies. No integer parameter occurs, and no nonzero, exactness, coequalizer, or symmetric-braiding hypothesis is needed. Verdict: no lost edge case and no additional hypothesis.
- Citations and form: verified the sole quotation in `citations.json` is literally a substring of the cited node's current statement and includes both the right-action formula and the definition of symmetry. Read the item JSON against its blueprint source; its TeX, dependency, and source paths are correct. Verdict: keep the citation and the existing mathematical proof unchanged.

Changes and reasons:

- Added an independent LeanFinder query and its actual result to the existing item's search record; kept all actual search-log entries. Three initial calls in this reading mistakenly supplied `--query`/`--sub` to a positional-only wrapper. Their logged queries are literally `--query`, so their irrelevant outputs are not evidence of absence; all three calls were rerun correctly.
- Added this current second-reading section with per-step and node-inventory verdicts, source comparison, and edge-case checks. Preserved the first worker's `## Review by Q26` and the earlier-round history.
- Kept the already-correct statement, identity-morphism proof, dependency, and verbatim citation unchanged. Final inventory: zero new nodes, zero new Mathlib leaves.

The installed delivery wrapper accepts group and item plus optional `--no-push`; its supported invocation omits the trailing literal dot in the brief. Validation and delivery are run through that wrapper, with no Lean writing or compilation.
