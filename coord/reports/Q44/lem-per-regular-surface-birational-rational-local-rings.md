# Stage-1 report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-surface-birational-rational-local-rings.json`: statement, split; statement unchanged. No Mathlib match.
- `citations.json`: verbatim statement quotations for all seven step citations.
- `report.md`: this report.

No new nodes and no new Mathlib leaves. The sandbox had no earlier item or report; the current repository item was the starting copy. Its inherited searches, citations, creation record and blueprint ancestry were retained. Five searches actually run for this delivery were added, with their logged digests.

## Attachments

None. Searched the slopmaster2 `WeilConjectures/` source for the exact item id and for rational singularity/rational surface vocabulary; no declaration states this item. Also checked the read-only master source and the upstream declaration-name inventory; no attachment candidate. No Lean was written or compiled.

## WANTED

None. All sources used are available in the repository.

## Problems found and corrections

The original item had an empty proof but an accurate statement and accurate Stacks source places. The DAG already has `lem-per-regular-surface-rational` (0B4Q), `lem-per-rational-singularity-birational-propagation` (0BG0), and `def-per-rational-surface-singularity` (0B4N). I reused them instead of adding duplicate or clause-restating nodes. I made the excellence-to-Nagata prerequisite explicit using `def-exc-excellent-ring` and `lem-exc-quasi-excellent-nagata` (07QV). The latter is declared as a generic off-unit tool in `split_report.tool_uses`; no unit proof step is replaced.

There is no statement dispute or source error. The blueprint ancestor and the inherited exact surface-resolution place remain unchanged; whole-blueprint searches for `rational singularity`, `regular surface`, `0B4Q`, and `0BG0` found no other blueprint statement of the item. The unit is Fourier exactness on a curve; this item is a lower-level surface input to its existing potential-dualizing construction, not the unit's key statement, so no unit record is changed.

## Not duplicates

No new nodes. Existing general propagation, regular-surface rationality and the rational-singularity definition are cited directly. This item specializes those independent existing inputs to an excellent regular base and spells out the universal vanishing, rather than moving its content into a new node.

## Unfinished work

None in the one-level split. The cited unsplit nodes remain separate DAG items. The required dry run exited successfully: server preflight passed at commit 67a5c92850. The final push is performed by the required delivery tool.

## Review by Q44

I read `resolve.tex` at the normal-modification convention in section-vanishing, Definition 0B4N (`definition-reduce-to-rational`), Lemma 0B4Q (`lemma-regular-rational`) with its proof, and Lemma 0BG0 (`lemma-rational-propagates`) with its proof. These are exactly the source route already specified by the item. I also read `more-algebra.tex` at 07QV (`lemma-quasi-excellent-nagata`) and the excellence definition recorded in `def-exc-excellent-ring`. No new node needs a separate source.

For Step 1 I opened both cited node statements. The excellence definition explicitly includes quasi-excellence and Noetherianness; 07QV's node states that a commutative quasi-excellent ring is Nagata. Hence it applies to the assumed excellent commutative ring R. I did not pretend Nagata was part of the definition of excellence.

For Step 2 I opened `lem-per-regular-surface-rational`: its assumptions are precisely a Nagata regular local ring of dimension 2, and its conclusion is the rational-singularity predicate. Nagata comes from Step 1; regular locality and dimension 2 are hypotheses of the item. I opened the predicate's definition as well: it includes the normal local surface domain setting and quantifies over all normal modifications, not just one resolution. Thus Step 2 uses the complete stated theorem and its defined conclusion; it does not mine that theorem's proof for a stronger interface. The theorem itself supplies rationality for a regular local ring, so a separate unproved regular-implies-normal step is not inserted.

For Step 3 I opened the propagation node and compared it word for word with Stacks 0BG0. Its base is a normal Nagata local domain of dimension 2 defining a rational singularity, supplied by Steps 1–2. Its extension is injective and local, consists of domains with the same fraction field, is essentially of finite type, is normal, and has dimension 2. All extension hypotheses are explicitly in this item. The source does not require B to be regular or the map Spec B to Spec R to be proper. I did not add either assumption. The conclusion is rationality of B, exactly what the final step needs.

For Step 4 I reopened the rational-singularity definition and `def-sc-topological-abelian-cohomology`. The former explicitly defines a normal modification by properness, integrality/normality and the function-field isomorphism, and gives universal H^1 vanishing; the latter explicitly identifies ordinary topological abelian cohomology on a scheme with its small-Zariski-site cohomology. Substituting the arbitrary (Z,g) from the conclusion into the universal predicate is elementary. There is no hidden comparison theorem or claim about etale coefficients.

For delivery-errors B, no statement-only new node is being smuggled in with a proof, no unnamed data or notions have been introduced, the item's existing definition citations are retained, and the mathematical statement was not altered. JSON uses single TeX backslashes. For C, every non-elementary input is an actual cited theorem statement; every use has a full verbatim quote in citations.json, and proof_deps is precisely the union of uses. The existing cited nodes do not depend on this item; no new cycle is introduced. The single off-unit theorem is the general Nagata tool declared above. For D, the proof has three applications of distinct existing inputs followed by definitional evaluation, with no new clause-restating lemma and no use of an omitted source argument. For E, I checked the dimension, normality, locality, finite-type-localization and fraction-field hypotheses individually as above. I tested the boundary case B=R and the identity modification Z=Spec B: propagation then adds no hypotheses, and the same universal predicate specializes correctly. Singular normal B is permitted throughout; no step assumes it regular. Dimension-one B and a nonlocal inclusion are excluded by the actual statement, so the propagation lemma is not misapplied in those cases. Every proof step is under 2000 characters and no separate lemma is hidden in a long step.

I read all five new logged Mathlib search results (LeanFinder twice with different phrasings, LeanSearch, Loogle, and source grep). Smooth-chart, normalization and cotangent-cohomology signatures are not structure-sheaf H^1 vanishing on normal proper models; Loogle and grep had no hits. The inherited searches were preserved, not represented as searches run by me.

## Validation

`deliver.py Q44 lem-per-regular-surface-birational-rational-local-rings --no-push` exited 0 and printed `OK (not pushed)` at 67a5c92850 after server preflight. The item has no step longer than 2000 characters. After the dry run, the only report correction was eight to seven citations and recording this validation; the node and quotations were unchanged.
