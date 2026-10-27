# Q114: lem-trf-critical-coset-infimum-calculus

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-critical-coset-infimum-calculus.json`: statement; split into six steps, statement and statement dependencies unchanged; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-binomial-root-correction.json`: new statement-only analytic root-lifting lemma; unsplit, no Mathlib match.
- `citations.json`: verbatim statement quotations for steps 3 and 6, the two remaining calls to root correction (after the repair below).

There is one new node and zero Mathlib leaves. No Lean file was written and no compiler, Lake or build command was run. All writes are in this item's sandbox.

## Attachments

None. Searches of `lean/WeilConjectures/` for the item's blueprint tag, critical cosets, critical polynomials, Temkin, infima, nonarchimedean fields and root/Hensel terminology found no declaration stating the item or the new lemma. Existing Henselian local-ring root lifting assumes henselianity of a ring and does not give the needed analytic complete-field estimate.

## Literature

WANTED: Michael Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3, the local copy `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, printed pp. 37–38, for both this item and `lem-trf-binomial-root-correction`. That named PDF is absent from this machine's read clone. I read those pages online in the author's PDF at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf, including the definition, both clauses of Lemma 6.1.2, its preliminary claim, and its proof. I have not downloaded or written a literature file. The proof is marked agent-origin because it expands the calculations and repairs an inference rather than copying the printed proof.

I also read the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md` and its proof, and the chapter/unit records. The latest blueprint's local-term proof now quotes Varshavsky's contracting theorem directly; the item is an existing descendant of the inherited semistable-modification route. This delivery retains that assigned branch and records the precise Temkin input and the full inherited ancestor chain. It changes neither the unit nor the chapter.

## Source error

The statement needs no correction. In the printed converse of Lemma 6.1.2(i), the first cancellation case invokes (ii), though criticality is what the converse is still proving. The final case also writes an equality between the polynomial infimum and the coefficient threshold which is not among its assumptions. I do not rely on either inference. In step 6 an inadmissible norm-improving shift satisfies |c|^p > |b| and |ac| = |c|^p; root correction then produces a root in F, contradicting the strictly positive unrestricted infimum. This proves admissibility and the equality of infima directly. The coefficient bound in step 3 is established for attained as well as unattained infima, using a representative close enough to s and root correction at c=v/a. Thus there is no assumption that a critical coset must contain a representative with norm strictly larger than s, nor any use of nondiscreteness to assert an unattained infimum.

## Mathlib and duplicate searches

All new searches were run through the required msearch.py and are in searches.jsonl. I read their returned names and signatures and inspected `Mathlib/NumberTheory/Padics/Hensel.lean:454–471` and the Henselian class declarations in `Mathlib/RingTheory/Henselian.lean:90–115`. `hensels_lemma` has roots specifically in the p-adic integers; it cannot specialize to an arbitrary complete nondiscretely valued field. `HenselianLocalRing.is_henselian` requires the valuation ring to be Henselian and a monic polynomial over it. Deriving that instance from metric completeness and treating the normalized nonmonic polynomial is additional mathematics, not a one-line specialization. Polynomial derivative identities, Newton fixed-point identities, Witt-vector constructions and bounds on norms of existing roots do not prove the new assertion. A second semantic phrasing and a grep restricted to `Topology/Algebra/Valued` also found no analytic root-lifting theorem. Every recorded query was actually run; all services answered successfully.

Before creating the new node I searched the whole DAG's statement texts for Hensel, root, contraction, Newton, nonarchimedean, critical-coset and binomial notions, and searched the blueprint index for `critical coset`, `root correction`, `Hensel root`, `nonarchimedean` and `binomial`. No blueprint node states root correction. I read the related Temkin statements listed below. No Stacks tag is asserted for Temkin's analytic lemma: the algebraic Henselian statements are not the completeness-to-root estimate.

## Not duplicates

lem-trf-binomial-root-correction vs lem-trf-critical-coset-infimum-calculus: the new lemma lifts an approximate root under explicit derivative-dominance inequalities, without any coset, threshold s or criticality hypothesis; it does not assert any clause of the item.

lem-trf-binomial-root-correction vs lem-trf-analytic-critical-polynomial-minimum: the existing node proves attainment of a positive infimum over a special one-dimensional analytic field; the new node is a local root-existence estimate for any complete nonarchimedean field.

lem-trf-binomial-root-correction vs lem-trf-analytic-prime-coset-model: the existing node constructs a special coset for an immediate extension of degree p over fields with algebraically closed residue and divisible value group; root correction has none of those extension or residue hypotheses.

lem-trf-binomial-root-correction vs lem-trf-analytic-coset-generator-reduction: the existing node produces topological generators from special cosets over an algebraically closed ground field; it is not a lifting theorem for a polynomial near a specified c.

lem-trf-binomial-root-correction vs lem-trf-critical-coset-coefficient-normalization: that node makes a tame extension and rescales a critical coset; the new lemma neither changes fields nor assumes a critical coset.

lem-trf-binomial-root-correction vs lem-trf-immediate-prime-polynomial-obstruction: that node constructs a polynomial with an unattained positive infimum from an immediate extension; the new node concerns when a given approximate root lifts.

lem-trf-binomial-root-correction vs lem-trf-analytic-frobenius-schauder-basis: that node constructs an orthogonal basis in types 2/3; the new node is a root estimate without a basis or analytic dimension hypothesis.

lem-trf-binomial-root-correction vs lem-trf-analytic-type23-stability: that node proves the degree formula for extensions of type 2/3 analytic fields; the new node is independent of that degree formula.

## Review by Q114

I read Temkin's actual definition and Lemma 6.1.2 on printed pp. 37–38, and checked the new root-correction statement against the preliminary Hensel argument on p. 37. The new statement makes the analytic hypotheses explicit instead of presupposing that a valuation ring is henselian. It is left statement-only. Its statement dependency `def-weil-field` really defines a field; the item's unchanged `def-trf-valuation-ring` really defines valuation rings. All other analytic notions are defined inline, including the metric, absolute value inequalities and the residue quotient in the item. No definition node is used as a theorem.

Step 1 uses no non-elementary input. The binomial identity gives the addition error bound because p divides each interior binomial coefficient; multiplying a sum of these terms by an integer of norm at most one preserves the maximum bound. The inverse calculation separately checks p=2, where the error is -2c^2 rather than zero. The residue characteristic gives p prime and |p|<1. These are elementary field, residue and norm calculations, so creating separate nodes for them would add unnecessary elementary nodes.

Step 2 uses the subgroup just proved. A vector of norm below s can be removed by the allowed small-error term, which proves the split criterion. In a nonsplit coset every restricted polynomial value has norm at least s and adding an error of norm below s leaves its norm unchanged. This supplies exactly the restricted infimum and the change-of-representative statement, without citing any unstated translation theorem.

Step 3 cites only `lem-trf-binomial-root-correction`. I opened its completed statement and checked that it provides both a root and the equality |z|=|c|; both are in the verbatim quotation in citations.json. Here c=v/a is nonzero, its (p-1)-st norm power is strictly below |a|, and the residual norm is |c|^p<|ac|. Completeness and |p|<1 come from the item. Choosing v below both the coefficient threshold and s/|p| is justified directly by infimum s; the |p|=0 case is treated without division. The root remains admissible, so it really splits the original coset.

Step 4 now uses no external theorem. I checked the coefficient bound already proved in step 3: if |c|^p<=s, both terms of P(c) have norm at most s, contradicting the norm-improving shift at a representative with norm above s. Thus |c|^p>s, and the coefficient bound makes |ac|<|c|^p. The ultrametric equality gives |v|=|c|^p and therefore the desired strict p-bound. The case |v|=s uses |p|<1 directly. This is an elementary consequence of earlier steps, and the unused citation of root correction has been removed from both the step and citations.json.

Step 5 is elementary assembly of steps 2–4. An unrestricted value below s must come from an inadmissible c. Its p-th power is strictly larger than s; the established coefficient bound makes the linear term smaller, so the constant term has exactly the p-th-power norm, violating the strict p-bound. Every use refers to a fact proved earlier in this item's proof, not to the proof of a cited node.

Step 6 makes the second remaining call to root correction. Its approximate-root point is nonzero because the p-th-power norm is greater than |b|>0. Both dominance hypotheses hold by exact cancellation of the two large terms. The root need not be admissible in this application: any root contradicts positive unrestricted infimum. This repairs the printed converse. Restricted values tending to s then give a nonsplit critical coset; the attained case |b|=s is supplied by c=0. The citations file quotes the actual new statement, and proof_deps is exactly the union of the two remaining uses. No off-unit statement tool is needed.

For the new lemma I also checked its mathematical consistency directly: after replacing T by cU and dividing by ac, the polynomial has the form h(U)=alpha U^p-U+beta with |alpha|<=1, |h(1)|<1 and |h'(1)|=1 since |p|<1. Writing U=1+u, its expansion has constant norm delta<1, unit linear coefficient D, and higher coefficients of norm at most one. If delta=0 use u=0. Otherwise on the closed delta-ball, the iteration u -> -D^{-1}(h(1)+sum_{i>=2} h_i u^i) preserves the ball and has Lipschitz constant at most delta<1; its iterates converge by completeness to a root, with |u|<=delta<1. This verifies the new lemma independently without putting a proof into its statement or creating a second nested split. It covers the boundary |c|^(p-1)=|a| and both equal and mixed characteristic, and requires no algebraic closure, no residue perfection and no discrete value group.

I checked B–E against the written files: the new node introduces every object, has no embedded proof, has actual searches of all four tools, and is strictly smaller than the item. All non-elementary steps cite the same precise root-lifting theorem with verified hypotheses; the other steps are explicit algebra and infimum arguments. Neither root-lifting nor criticality is invoked circularly. The cases a=0, b=0 (which cannot satisfy criticality or a positive polynomial infimum), c=0, p=2, |p|=0, |v|=s and unattained s have all been checked. No step exceeds 2000 characters and no further comparison or identification is hidden in a long step. The item's full statement is unchanged, so no STATEMENT-DISPUTED correction is needed.

## Remaining work

Only the new root-correction node remains unsplit, as required for a one-level stage-1 split. It is non-elementary analytic root existence, not a restated clause of this item. Validation and delivery follow through the prescribed server tools.


## Repair of return at 7dd67f709c0

The return dated 2026-10-24 10:11 UTC says the reader approved the mathematics, but landing reported: “completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it)”. The requested action was to rebase onto the current DAG, reread changed citations, adjust the split and push again.

I retained the returned proof, report, citations, new node and search log. The required diagnostic dry run was run first on those retained files and passed at 4cfd815efec. I compared the retained item with the current read clone: statement, stmt_deps, source, blueprint ancestry, creation record, chapter and unit were identical; the current item still has status unsplit, proof [], and no reviewed record. The new root-correction node remains absent from the current read clone, so it has not been superseded by a landed duplicate. I refreshed the item from the current record while retaining its authored split fields; the delivery tool independently fetches and overlays those fields on current origin/sheaf-dag.

I reread the full statements of def-weil-field and def-trf-valuation-ring and the retained lem-trf-binomial-root-correction; the first two retain their original definitions and the third still supplies a root and equality of its norm with the approximation point. Thus there is no changed mathematical hypothesis to propagate. I reused the actual recorded Mathlib searches because neither the lemma statement nor the search question changed.

The repair also changes the proof substantively: step 4 now derives the strict p-bound directly from the previously proved coefficient estimate, eliminating an unnecessary root-lifting invocation. I checked both cases |c|^p<=s and |c|^p>s and the endpoint |v|=s, and removed the obsolete citation from citations.json. Steps 3 and 6 still invoke the exact same verified root-correction statement, and proof_deps remains their union. All six steps remain shorter than 2000 characters; the new node remains statement-only.

The completion/promotion discrepancy itself belongs to the maintainer: I have not changed a queue, completion record, review field, launcher script or landing tool. If it recurs after this rebased delivery, L must reconcile the reported completion with the DAG read by the queue, as the return itself specifies. This resubmission supplies the current split and an actual proof adjustment, without claiming that a worker can repair the maintainer's two-view bookkeeping.


## Delivery retry after server storage failure

The previous repaired push was rejected by the remote unpacker with “No space left on device”; it did not deliver a replacement branch. On this retry I verified that the substantive step-4 repair and the two-entry citations file remain intact. I reread all three cited statements against the current read clone/sandbox and found no statement changes. The current item remains unsplit and the new root-correction node remains absent from the read clone. The retained split passed the required initial dry run again at 1816d9327bd. The prior actual search log is retained without inventing or repeating searches. This retry continues the repaired delivery, rather than restoring the returned proof or changing maintainer-owned promotion records.


## Repair of repeated return at e460d52e6bc

The repeated return is dated 2026-10-24 10:48 UTC. I compared the retained split with the current read clone again. The current item remains unsplit, without review, and the root-correction node is still absent. Statement, statement dependencies, source, blueprint chain, unit and chapter are unchanged. I reread the full field, valuation-ring and root-correction statements; no citation or hypothesis changed. The initial diagnostic dry run passed at 204a82b08bf.

I retained the substantive step-4 repair already delivered at e460d52e6bc. I also replaced the phrase “letting r decrease to s” in step 6 by its explicit quantifier argument: for each t>s choose s<r<min(t,|b|), obtain an admissible value below t, and combine this with the unrestricted lower bound. This removes any implicit sequential-limit assumption and directly proves the equality of ordinary real infima. The attained case |b|=s is handled separately as before. Citation quotes and the two remaining root-correction applications are unchanged.

For the repeated landing refusal I read tools/nt_land_batch.py and tools/dag_queue.py without running or changing them. In nt_land_batch.land_chunk, s1 is the set of ids returned by Dag(load()).stage1(); an id absent from s1 enters notopen. In the later notopen handler (lines 559–572 in this read clone), when retirement fails and queue_node(item) exists but is not stage1_completed, the tool emits the quoted “completed in this project's DAG but not in the live DAG” message. That branch does not independently check that the project's own node is completed. Stage-1 queue membership also depends on target reach and ancestor traversal, not just the completion predicate, so this diagnostic is not proof of a side-only completion. The read clone has an unsplit item and reviewed split immediate parents, and no released repair note for this id. Any remaining server queue-membership or promotion discrepancy must be handled by L in the landing/queue state; it cannot be corrected by changing this lemma's hypotheses or setting worker-owned proof fields. I did not alter another node, a repair note, a review record, a script or queue settings. This report supplies the exact diagnostic control flow for L's investigation while the updated split is rebased by the prescribed delivery tool.


## Repeated landing refusal at 5117f6b7b0e

The return dated 2026-10-24 10:57 UTC again approves the reader's review and rejects landing with the same queue/completion diagnostic. On this retry the required initial dry run completed successfully at 8955c6ddf73. I compared the retained item with current main again: statement, statement dependencies, source, blueprint ancestry, creation record, chapter and unit agree exactly. Main still records an unsplit item with no review, and still has no root-correction node. I reread the full statements of def-weil-field, def-trf-valuation-ring and the sandbox root-correction node; the hypotheses and conclusions used by steps 3 and 6 are unchanged, and both citation quotes remain verbatim. The substantive repairs to steps 4 and 6 are retained; no mathematical repair has been reverted.

The landing failure persists outside the item files. Reading nt_land_batch.py shows that queue nonmembership sends a delivery to notopen before prepare; its later diagnostic chooses the side-completion wording whenever the queue copy exists and is incomplete. It does not establish side completion. A read-only traversal of the current DAG shows this item is reachable from the configured targets before finished-node pruning and is not itself listed in coord/route-pivot-dropped.txt; no repair note for this item exists. I cannot infer the server's exact pruning or configuration state from the read clone. The maintainer must inspect the stage1() exclusion on the landing server and reconcile queue admission or release the appropriate repair state. Changing this item's proof, hypotheses or citations cannot change an admission decision made on main before the delivery is prepared.

This is a landing/queue blocker, not a failure of the approved split. I have recorded it instead of making another cosmetic proof edit or changing a maintainer-owned queue, completion, review, repair-note or tool record. The sandbox preserves the complete reviewed split, report, actual search log and verified citations for delivery once admission is repaired.


## Resumed delivery after dry-run-only blocker

The dispatcher explicitly requested another delivery after the previous attempt stopped at successful dry run 4695ab0a1ef. That attempt had no interrupted push to resume. I ran the required initial diagnostic dry run on the retained sandbox; it passed at 526b9367463. I compared all item fields with the current read clone: only the authored split fields differ (proof, proof dependencies, proof origin, search records, split report and status). The mathematical interface and all upstream metadata agree. Main still records this item as unsplit without review and has no root-correction node. I reread both statement-dependency definitions and the root-correction statement, rechecked both verbatim citation entries and their step numbers, and retained the previously logged searches because their questions and statements have not changed.

This submission retains the actual proof repairs made after the original return: the direct coefficient-bound argument in step 4 and the quantified approximation argument in step 6. The retained split is not the original returned proof. No additional mathematical defect was found during this retry, and I have not invented a new proof change to disguise the unresolved landing diagnostic. The report's earlier diagnosis records what the read-only tool inspection established and what remains unknown on the server. The requested push now submits these repaired item files and this current comparison to the maintainer; it does not assert that the worker has changed queue admission or promoted a completion.


## Landing refusal of 04c47a92e4c

The return dated 2026-10-24 11:14 UTC confirms that the explicitly requested push 04c47a92e4c reached the reader and was approved, but landing again refused it with the identical queue/completion diagnostic. Thus the previous resubmission did exercise the push path; there is no interrupted deliver.py invocation to resume. On this retry the required first diagnostic dry run passed at e4b86271814.

I compared the retained delivery with the current read clone and reread every cited statement. The current item is still unsplit and unreviewed; statement, statement dependencies, source, blueprint, creation record, unit and chapter remain identical. Both cited definitions are unchanged. The new root-correction statement is retained in the sandbox and remains absent upstream. Its two verbatim quotes and the hypotheses checked in steps 3 and 6 still match. The genuine proof corrections in steps 4 and 6 remain intact. No fresh Mathlib search is warranted because no statement or search question changed. No repair note for the item exists in the read clone.

The repeated refusal occurs before the landing tool prepares this delivery, on the main DAG's stage1() membership test. Another alteration of worker-owned proof fields cannot affect that decision. The tool's subsequent side-completion wording does not distinguish completion from other causes of queue exclusion, as the control-flow analysis above documents. I cannot repair or truthfully claim to repair server queue admission from this sandbox. The prescribed response to a tool or gate that appears wrong is BLOCKED, without patching or working around it. The maintainer must inspect the item’s exclusion from stage1() on the landing server and reconcile the completion or queue state before another submission can land. The complete approved mathematical repair and all actual searches remain preserved here.


## Landing refusal of e88839d9266

The return dated 2026-10-24 11:25 UTC again records reader approval and the identical landing refusal for the actual push e88839d9266. That push exited successfully, so no interrupted delivery remains active. The required first dry run on this retry passed at faa9ae56d6b. I compared every field of the current item with the retained delivery: all statement and provenance fields agree; only the authored split fields differ. I reread the complete field, valuation-ring and root-correction statements and checked each quotation against the exact cited statement and its step number. No citation or mathematical hypothesis changed. The current item is unsplit without review, the new root-correction node is absent upstream, and no repair note for the item exists.

The two substantive mathematical repairs already documented remain preserved. The new return supplies no mathematical correction to make, and it confirms that a fresh push of those repairs did not resolve the admission discrepancy. A further proof alteration would not repair the stage1() membership test on main before prepare. The brief explicitly forbids patching or working around a wrong gate and requires reporting it as BLOCKED. I therefore preserve the approved split and actual searches and report the repeated landing/queue failure, pending L's reconciliation or promotion of the state named in the return.


## Explicit root-correction hypothesis checks after e88839d9266

The new dispatcher request asks for another actual submission after the dry-run-only blocker. The required first dry run on the retained files passed at 3784397f965. I again compared the statement, statement dependencies and provenance with current main, reread every cited statement, and checked both verbatim citation quotes. None changed; main still has an unsplit, unreviewed item and no root-correction node or released repair note. The earlier delivery process exited, so no invocation was left active.

This revision makes two previously implicit hypothesis checks explicit in the item itself. In step 3, |v|<A implies |v|^(p-1)<|a|^p, whence |c|^p=|v|^p/|a|^p<|v|. This is the precise comparison used to make the root admissible. In step 6, the large p-th-power norm proves c is nonzero, after which division by |c| turns |ac|=|c|^p into the root-correction coefficient hypothesis. Both arguments were checked against the root-correction statement; they use only elementary positive real inequalities and multiplicativity, introduce no new dependency, and leave both citation entries unchanged. The earlier substantive repairs remain intact. No new search is needed because no statement or search question changed.

These proof clarifications do not claim to repair the main-DAG queue gate. Its repeated refusal and the maintainer action needed are documented above. The prescribed delivery tool will rebase and submit this explicit revision; no queue, completion, repair note, review field, launcher or repository file was changed by this worker.


## Landing refusal of 20fa240a139

The return dated 2026-10-24 11:46 UTC confirms that the reader approved the revised split at 20fa240a139, including the explicit root-correction hypothesis checks, and landing again rejected it with the same queue/completion diagnostic. The preceding push exited successfully; there is no interrupted invocation to resume. The required initial diagnostic dry run on this retry passed at 8d498a4b69a.

I compared the retained item against current main and reread all cited statements. The statement, statement dependencies, source, blueprint, creation record, chapter and unit are unchanged; main still records the item as unsplit without review. Both cited definitions and the sandbox root-correction statement supply the same hypotheses and conclusions. Both quotation entries remain verbatim and refer to the correct steps. The root-correction node is absent upstream, and no repair note for the item exists. The explicit estimates added in the previous revision remain intact. There is no new mathematical defect or changed citation to repair.

This latest actual push demonstrates again that editing and rebasing the approved item does not resolve main-DAG queue admission. I cannot promote a completion, release a repair note or alter the queue from the authorized sandbox. The brief requires a wrong gate to be reported as BLOCKED without patching or working around it. All mathematical work is preserved for L to land after reconciling the state named in the return. Another unchanged push would not constitute the requested repair.


## Landing refusal of fd7d1ed036f

The return dated 2026-10-24 11:58 UTC confirms reader approval of fd7d1ed036f and another identical landing refusal. The push process exited successfully; there is no unfinished delivery to poll. The required diagnostic dry run on the retained sandbox passed at e4b32640ef1. I compared every item field with current main, reread the two statement-dependency definitions and the root-correction statement, and verified both verbatim quotations and their step numbers. The statement, dependencies of the statement and all source/blueprint metadata remain unchanged. Main still records an unsplit, unreviewed item; the new node and an item repair note are absent upstream. Every previous mathematical repair remains in the sandbox.

I reread the current nt_land_batch.py admission branch and its notopen diagnostic. It still tests membership in the main DAG's stage1() set before preparing the worker delivery. When retirement fails and the queue node is incomplete, it emits the side-completion message without independently establishing a completed project node. No permitted edit of this item's proof can alter that earlier decision on main. The read clone's cached closed-module data is not enough to establish the server's exact pruning state, and I have not treated it as such. L must inspect the exclusion on the landing server and reconcile the queue/completion state or release the appropriate repair state.

The brief forbids an unchanged resubmission as a repair and forbids patching or working around a wrong tool gate. I therefore preserve the complete approved split, citations and actual searches and report BLOCKED rather than manufacturing another mathematical change or another identical submission.


## Maintainer precedent for the queue-reach blocker

A further read-only investigation found completed maintainer repairs for this exact class of failure in coord/maintenance/20261024-Q103-critical-coset-reach.md and coord/maintenance/20261024-N6-affinoid-unit-ball-reach.md. Q103's related critical-coset-coefficient-normalization assignment was incomplete in both DAG views but excluded from active queue reach through withdrawn ancestors and the batch-5 trace-transport assumption. The maintainer record explicitly identifies the side-completion diagnostic as misleading and states that rebasing the worker split cannot repair eligibility. It records a supported coord/preopen.txt root preserving the approved assignment, followed by replay of its exact independent PASS through unchanged normal landing tools. N6 records the same supported coordination repair and successful landing.

The current coord/preopen.txt contains those preserved assignments but does not contain lem-trf-critical-coset-infimum-calculus. This item remains unsplit and unreviewed in the read clone, its interface is unchanged, and it has no released repair note. I have not run the real stage1 predicate locally because its helpers can write caches and run git; nor do these analogous records establish the exact current server exclusion for Q114. They provide a concrete maintainer-owned investigation and repair route: inspect this item's active reach, preserve the explicitly assigned approved delivery through supported reach coordination if appropriate, then replay the recorded independent review of 64538205eb0 through normal landing. No mathematical rewrite or identical push can change the pre-application eligibility decision.

Only this sandbox report was updated. No coord file, queue setting, completion record, tool, launcher or Lean source was edited. The approved split, substantive earlier repairs, citation quotes and actual search log remain intact.
