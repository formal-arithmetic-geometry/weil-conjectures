# Worker report: prop-zl-smooth-proper-relative-purity

## Files written

- dag/nodes/sec-zeta-weil/prop-zl-smooth-proper-relative-purity.json: item, statement, split into eight steps; no Mathlib match.
- dag/nodes/sec-zeta-weil/lem-zl-adic-hom-tensor-lisse-criterion.json: new statement-only coefficient-category lemma; no Mathlib match.
- dag/nodes/sec-zeta-weil/lem-zl-lisse-cohomology-derived-dual.json: new statement-only coefficient dual/cohomology lemma; no Mathlib match.
- dag/units/sk-prop-smooth-proper-purity.json: only realized and realized_by filled. The sandbox copy is refreshed from the corrected authoritative unit; its five current paragraph bindings are realized by the item. Step 8 only specializes the relative proof. No unit statement, route or dependency is changed by this delivery relative to current main.
- citations.json records one exact statement substring for each proof-step citation. searches.jsonl is the unmodified search-command log.

## Attachments

None. I searched WeilConjectures for the blueprint id and smooth/proper/purity wording, then read ZetaLinearAlgebra/Purity.lean in the read-only slopmaster2 checkout. TraceDatum.isPureOfWeight_map_P_of_pairing is a linear-algebra theorem conditional on a pairing and degreewise mixedness. It states neither relative higher direct images nor lissity of their cohomology sheaves, so is not an attachment. The existing Poincare/Perfect declarations likewise do not give the two coefficient lemmas in the raw rational/common-stage categories.

## WANTED

None. The current blueprint proof, Hemo--Richarz--Scholbach, Bhatt--Scholze and the relevant Stacks source are present locally.

## Source error and repair

STATEMENT-DISPUTED: the current blueprint proof's Step 1 inference “since F is lisse, choose a global lisse integral lattice” is false for the pro-etale lisse notion on nonnormal schemes. The theorem statement itself is unchanged and is not disputed. This distinction matters because Y is permitted to be singular and X need not be normal.

The explicit counterexample is the one already stated in sk-lem-stratified-lattice: glue 0 and infinity on P1 to a node, take its infinite-chain etale Z-cover, and descend a constant E-line with the generator acting by multiplication by ell. A lisse lattice pulled to the connected chain is a constant lattice pi^m O_E; it cannot be preserved by both ell and ell inverse. Bhatt--Scholze p.61 preceding Lemma 6.8.13 explicitly distinguishes a constructible integral model from a lisse integral model. The current proof also passes cohomology through an inverse limit without a justification of that passage. I do not carry out either inference.

Steps 3--4 instead use the relative smooth orientation and tensor--Hom duality already required in unit Step 3, for variable N, followed by the field projection formula. This proves the canonical internal-Hom/tensor comparison for K=Rf_*F. A general coefficient-category criterion then proves its cohomology lisse. This repairs the rational local-constancy passage without a new hypothesis or a smooth-proper pushforward lemma restating clause (a). It does not change the chapter route or the weight argument. The finite smooth-base-change foundation remains part of the established purity/six-functor route; this delivery introduces no new trace/purity route, and cites no SGA source. The split_report.source_error field now explicitly records the failing inference and replacement, rather than silently changing the imported argument.

The long imported duality step also hid the natural bounded truncation comparison between cohomology of a derived coefficient dual and the linear dual of cohomology. It is now its own generic coefficient lemma. No new node restates smooth-proper purity or one of its geometric clauses.

## Search and duplicate audit

I searched the whole DAG by smooth proper, specialization/local constancy, lisse and lattices, dualizable, derived dual and cohomology/Hom wording, and ran blueprint_refs searches for smooth proper, dualizable, cohomology dual, lisse cohomology, Hom tensor, dual cohomology, derived dual and 08JI. blueprint_refs ancestor confirms that both new nodes descend directly from this item's blueprint id. same_as is empty: the current proposition is the relative theorem; cor-zl-purity-smooth-proper is its absolute constant-coefficient consequence. Every new node's exact source position is recorded.

I found and read the finite-coefficient specialization and finite-stalk criterion nodes, but did not duplicate them or extend their statements to rational coefficients. I also read prop-sf-dualizable, prop-sf-dualizable-hom, lem-sfb-ringed-site-perfect-duality, lem-sfb-internal-hom-dual-constructible-models, lem-pod-cohomology-of-dual-over-field and lem-per-adic-lisse-cohomology-calculus. The first three prove forward perfect-duality assertions, not the converse adic lissity criterion. The latter three concern respectively specified scalar perfect local models, a vector-space complex at a point, and tensoring with one lisse sheaf; none states the bounded sheaf-level dual cohomology comparison in the raw rational/common-stage category.

For the item and each new node I ran LeanFinder, Loogle, grep and LeanSearch through msearch.py, including a second natural-language phrasing. Searches and actual hit names are recorded verbatim in mathlib_searches and searches.jsonl. All services answered. Hits include generic module/sheaf pushforwards, ordinary derived bounds and Hom complexes, opposite complexes, group cohomology/Ext, and light-condensed module structures. None is an exact match or a one-line specialization to these adic assertions. In particular HomologicalComplex.homologyOpNatIso computes the opposite of a complex, not the coefficient derived dual. LightCondensed's closed monoidal structure is not a lissity theorem on a scheme. No Mathlib leaves are claimed.

## Not duplicates

The source's 08JI is only a local computational ingredient, not an assertion of the new adic theorem. I read all same-tag statements:

lem-zl-lisse-cohomology-derived-dual vs prop-sf-dualizable: the existing node proves perfectness of a dual, not H^{-i}(K dual)=(H^i K) dual.
lem-zl-lisse-cohomology-derived-dual vs lem-sfb-constructible-internal-hom-continuity: filtered colimits in the second variable, not dual cohomology.
lem-zl-lisse-cohomology-derived-dual vs lem-fin-lisse-field-dual: existing result is ordinary etale F_ell coefficients; new result is the completed/rationalized/common-stage E or Qbar_ell category with Weil naturality.
lem-zl-lisse-cohomology-derived-dual vs det-lem-int-integral-heart-dualizable: an integral degree-zero stratum and Tor bounds, not the field-stage cohomology reversal for a bounded complex.
lem-zl-lisse-cohomology-derived-dual vs det-rem-sf-matrix-hom-devissage: finite torsion internal-Hom preservation, not dual cohomology.
lem-zl-lisse-cohomology-derived-dual vs lem-pod-point-completed-evaluation: equality of evaluation maps at Spec k on an integral projective model, not a sheaf-level cohomology comparison on T.
lem-zl-lisse-cohomology-derived-dual vs lem-sf-etale-generic-perfect-hom: finite-coefficient pullback and amplitude for an etale perfect first input, not the rational/common-stage cohomology formula.
lem-zl-lisse-cohomology-derived-dual vs lem-weil-pbc-ringed-site-bounded-free-rhom-model: a Hom-complex model under termwise projectivity, not the cohomology comparison from lisse cohomology alone.
lem-zl-lisse-cohomology-derived-dual vs lem-sf-hom-comparison-finite-free: compares etale/pro-etale finite Hom; no dual-cohomology assertion or rational coefficient passage.
lem-zl-lisse-cohomology-derived-dual vs lem-sf-rational-term-hom-comparison: degree-zero term Hom comparison after scalar localization; no bounded-complex/cohomology statement.
lem-zl-lisse-cohomology-derived-dual vs lem-sf-hom-finite-projective: first input is one finite-projective module, not a complex known only by its lisse cohomology.
lem-zl-lisse-cohomology-derived-dual vs lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation: finite coefficient morphism/isomorphism sheaf evaluation on contractible covers, not derived dual cohomology.
lem-zl-lisse-cohomology-derived-dual vs lem-pod-coefficient-dual-perfect: perfect dual remains perfect; no identification of its individual cohomology sheaves.

lem-zl-adic-hom-tensor-lisse-criterion vs prop-sf-dualizable-hom: existing statement is the forward evaluation formula assuming site-perfectness; the new statement derives lisse cohomology from invertibility of that canonical formula and uses the Noetherian adic t-structure theorem.
lem-zl-adic-hom-tensor-lisse-criterion vs lem-pc-dualizable-evaluation-criterion: existing statement is about O_X modules and triangle identities; new statement concerns adic coefficient categories and lisse cohomology on the small pro-etale site. The former does not assert the coefficient-category comparison or adic t-structure consequence.

## Review by Q159

I read the sec-zeta-weil chapter record, all paragraphs of sk-prop-smooth-proper-purity, and the current main-20261015 statement and proof. The item retains smoothness, properness, separated finite-type schemes, pure relative dimension, arbitrary real weight, every integer i, and the geometric-Frobenius normalization. No normality, smooth base, connected fibre or admissibility assumption has been inserted. The absolute conclusion follows by specialization; the separate absolute-duality alternative has been removed as required by return R1.

For lem-zl-adic-hom-tensor-lisse-criterion I read HRS Definition 3.3 (derived lisse means dualizable), Theorem 6.2(2) and Corollary 6.3 (lisse cohomology when the base locally has finitely many irreducible components), Corollary 6.11 (the coefficient fields are t-admissible), and Theorem 7.7/Lemma 7.9 (classical/common-stage comparison). I read Bhatt--Scholze Proposition 6.8.14(2), pp.61--62, for raw localization without an invented Karoubi completion, and read the project's rationalization, Qbar pair-category and continuous coefficient realization statements. The criterion requires the canonical evaluation comparison for every bounded constructible N, not merely some isomorphism of endpoints. The induced duality lives in the constructible monoidal subcategory and its fully faithful monoidal realization, so the adic t-structure result applies. Finite type guarantees the Noetherian/component hypotheses; fields ensure finitely presented local modules are finite free. This is a comparison obligation for the next split, not claimed as already formalized.

For lem-zl-lisse-cohomology-derived-dual I read the current proof Step 3, Stacks 08JI (sites-cohomology-lemma-Rhom-complex-of-direct-summands-finite-free) in sites-cohomology.tex, and the existing finite-projective and finite-field dual statements. The new statement says exactly the natural comparison needed after all H^j(K) are lisse, not a general duality assertion for arbitrary constructible cohomology. The underlying proof is bounded truncation or the sheaf hyper-Ext filtration: locally projective cohomology makes all positive internal Ext columns vanish, leaving the degree-reversed dual column. Naturality in isomorphism pullbacks and coefficient changes supplies the Weil assertion; this is not an unsupported stalkwise dualization over a singular base. The local Stacks lemma alone does not supply its adic coefficient comparison, which is explicitly retained in the new node.

Step 1: I opened thm-sf-ctf-stability, cor-cbc-proper-coincidence and prop-weil-operations. The first supplies the bounded constructible field-stage domain; the second identifies the proper compactification and the two exchange maps; the third states the Weil isomorphisms are built from those maps. Therefore coincidence is Weil, not just an underlying isomorphism. The conditional nature of the operations theorem is not used to prove its own preservation premise.

Step 2: lem-sf-hom-finite-projective is valid in the rational/common-stage coefficient convention, not merely for discrete constant coefficients; its unit specialization identifies the derived and linear dual for the lisse input. lem-tw-dual-stalk-frobenius explicitly states lissity, invertibility, the dual stalk identification and the contragredient local action. lem-sf-twist-interchange explicitly identifies the Tate line as invertible and locally rank one at the field stages. lem-wf-tate-twist-frobenius gives q_x^{-d}, so the sign is -w-2d. Triangularizing an invertible finite matrix and reading its reciprocal diagonal is elementary; no new linear algebra node is needed.

Step 3: lem-sf-tensor-hom states the actual relative exchange for the unconditional constructible exceptional inverse image. thm-sf-ctf-stability supplies the field finite-Tor domains. thm-pur-rational-and-qbar-purity is for smooth separated pure-dimensional f and arbitrary normalized-integral presentations, all available here; it does not require lisse integral models. prop-sf-dualizable-hom is applied to the original locally finite-free F, not to the direct image whose lissity is still being proved. The resulting formula holds for variable N, and the unit case proves K dual bounded constructible. This avoids circular use of clause (a).

Step 4: thm-sf-pf-field explicitly treats raw rational objects and common finite stages. Every object used has an integral representative by the definitions, which is different from assuming a lisse integral lattice. prop-sf-pf-coherence explicitly identifies the proper projection formula with direct-image projection and gives coefficient compatibility. I checked the evaluation identity by transposing: both composites evaluate the F factor and then apply the same exceptional-adjunction counit, with 1_N untouched. This verifies the canonical comparison hypothesis of the new criterion. Its conclusion is exactly lissity of every H^i(K). This is a formal mate computation, not an unnamed geometric local-constancy lemma. No step is longer than 2000 characters.

Step 5: def-weil-punctual-weights really defines the finite filtration being used, and cor-zl-rfshriek-sheaf states weights at most w+i for every i under the separated finite-type hypotheses. Exact stalks give an invariant filtration; the adapted-basis block triangular determinant argument explains why each eigenvalue comes from a pure quotient. q_y>1 ensures the stated real-exponent inequality. Nothing here supposes that mixed sheaves are already pure.

Step 6: prop-weil-operations explicitly makes composition, purity and duality maps Weil; the new derived-dual lemma gives the natural cohomology identification and contragredient structure. Its boundedness hypotheses were established before lissity. The shift calculation is H^{-i}(B[2d])=H^{2d-i}(B), with no restriction to nonnegative i.

Step 7: the upper bound is applied again to G_0 of weight -w-2d in degree 2d-i. The dual-stalk statement makes the corresponding eigenvalue alpha inverse. Taking reciprocals gives the lower bound with the correct sign. The geometric-fibre Qbar statement was opened: its noetherian, finite-dimensional, proper-fibre and bounded-dimension hypotheses hold after base change, ell is invertible, and the fibre dimension is d. No ordinary discrete coefficient theorem is substituted for it.

Step 8: the constant coefficient input has identity Frobenius and weight zero, so specializing step 7 to the unique closed point of Spec k_0 gives the absolute conclusion with cardinality q. This is elementary and uses no additional node. I removed the independent absolute-duality alternative and its thm-weil-poincare-duality citation; nt-assume-poincare-duality is not a substitute because it excludes the pairing and Frobenius equivariance.

Small-case checks: empty T and zero K make both new statements vacuous or 0=0; variable rank and rank zero are allowed. For K=L[-j] with lisse L, the new dual formula is H^{-j}(L dual[j])=L dual, verifying the sign. At a point the criterion is ordinary finite-dimensional derived duality; on a singular finite-type scheme HRS still applies because finite irreducible components, not normality, are required. A constructible skyscraper is not falsely declared lisse: its evaluation criterion fails, so the new criterion has a substantive hypothesis. For f=id (d=0), the result reduces to the input weight and the two reciprocal estimates agree; for a zero input all eigenvalue claims are vacuous; for i outside the cohomological range all sheaves are zero. The singular nodal example was used specifically to reject the imported lattice inference, never to weaken the theorem.

I checked B--E: both new nodes are self-contained statement-only obligations with no hidden proof or proof dependencies; all introduced notions have definition/category dependencies or explicit descriptions. Every cited statement was opened, exact quotations are in citations.json, and the existing O_X, finite-etale, completed-integral, raw rational and common-stage assertions have not been conflated. No new declaration or compiler was run. The earlier delivery answered the unit-reach check by adding an absolute-duality alternative; return R1 correctly rejects that under batch 5. I removed it. I do not add an unused dependency or clear the realization bindings. The authoritative unit-route correction has now arrived; I refreshed the sandbox copy from that base and bound its five remaining paragraphs to the item.

## Unfinished work

The two new coefficient lemmas remain unsplit by design: this is a one-level stage-1 split. No Lean work is part of this delivery. Server validation results are recorded below after execution.

## Repair of return at 4503ca1ea9

R1: Removed the absolute Poincare-duality alternative from step 8, removed thm-weil-poincare-duality from uses and proof_deps, and marked the remaining absolute specialization elementary. No replacement by nt-assume-poincare-duality: its scope does not include this pairing. Steps 1--7 and both coefficient lemmas are retained; the reviewer found their mathematics sound. The report no longer claims to prove the removed alternative. I compared the retained nodes with current shared main: the item remains imported, both helper ids remain absent, and chapter/unit/source/statement and all imported metadata agree. deliver.py rebases the permitted split fields onto current main. The old unit record still cites sk-thm-poincare-duality, while the current main-20261015 proposition proof contains no independent absolute alternative. This is a maintainer-owned route inconsistency, anticipated explicitly by the return; the unit copy changes only realized and realized_by. A maintainer must decide and install the authoritative unit-route correction; a worker cannot edit its uses/steps or invent a citation merely to reach that unit.

R2: Added the actual split_report.source_error record in the node: exact failing lattice inference, nodal infinite-chain counterexample, f=id of relative dimension zero, valuation obstruction to a descended lattice, source position, and replacement argument. The proposition statement remains unchanged. The split_report.blueprint field now names this existing record precisely. The repair is recorded in the node as well as this report, as brief section 0 requires.

Minor: Removed both new same-unit coefficient lemmas from split_report.tool_uses; they remain ordinary proof dependencies at steps 4 and 6. Only genuine off-unit tools remain declared.

## Validation

The retained sandbox lacked citations.json, searches.jsonl and the unit file although its old report named them. The required initial dry run was run before repairs and exited 1 at SEARCH CHECK FAILED because the log was missing. I therefore reran all 15 exact recorded queries through msearch.py (including the item), read their results, and restored the command-generated search log. The same mathematical questions and two phrasings were retained. I restored the unit realization copy from current shared main and reconstructed exact citations from the opened statements. No Lean, build, compiler, live-repository edit or direct git command was run.

The repaired full dry run exited 1 with exactly one preflight finding (nothing pushed):

```
units: sk-prop-smooth-proper-purity cites sk-thm-poincare-duality, which its nodes do not reach
```

The command was `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q159 prop-zl-smooth-proper-relative-purity --no-push`; its process exited before this report update. Search-log verification and the 23 exact step/node citation quotations passed admission. Every proof step is below 2000 characters (maximum 1109). The item statement, both new statements, their search queries and results, and imported metadata remain unchanged; the requested proof/dependency/report repairs are present. No push invocation was made because preflight did not print OK.

BLOCKED pending the maintainer decision explicitly identified in R1: align the authoritative sk-prop-smooth-proper-purity unit route/absolute alternative with the current main-20261015 relative proof and the batch-5 restriction, then sync the corrected base. This worker cannot change the unit's uses, steps, statement, or maintainer bindings. Adding a forbidden/unused citation or suppressing unit realization would conceal the inconsistency. After that correction, retain this sandbox repair, refresh only its unit realization copy against the corrected record, rerun the normal dry run, and push only on OK.

## Final validation retry

I reran the required server check before delivery; it still reports exactly one finding: `sk-prop-smooth-proper-purity` cites `sk-thm-poincare-duality`, which the realized nodes do not reach. I then reran `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q159 prop-zl-smooth-proper-relative-purity --no-push .`; server preflight reproduced the same single `tools/check_dag.py` finding and admitted no commit. The item has no `thm-weil-poincare-duality` dependency or proof citation, the source-error record is present, and the new helper lemmas are absent from `split_report.tool_uses`. Resolving the remaining unit `uses`/route mismatch requires the maintainer-owned unit metadata decision identified in R1; changing realized bindings to fabricate a reach would misstate the proof.


## Retained-repair retry, 2026-10-18

I resumed the existing repair rather than rewriting the split or repeating its searches. I compared the sandbox item with the current shared item: the base remains imported, and the only differing fields are the worker-owned proof, proof_deps, proof_origin, status, mathlib_searches, blueprint and split_report fields. Neither new helper id exists in the shared DAG. The shared and sandbox unit records agree outside realized and realized_by; both still name sk-thm-poincare-duality in uses and the independent absolute-duality paragraph. No authoritative route correction has been installed.

I verified R1 directly in the retained proof: step 8 has no node citations and only specializes step 7; thm-weil-poincare-duality is absent from proof_deps and every uses list. I verified R2 in the actual JSON, not just this report: split_report.source_error contains the failing lattice inference, nodal infinite-chain counterexample, the f=id dimension-zero test, its source and the replacement argument. I verified the minor correction: neither of the two new same-unit helper nodes appears in split_report.tool_uses. Their ordinary proof citations remain at steps 4 and 6. The 15 command-generated search records and all citation records were retained unchanged. The longest non-elementary proof step has 1109 characters.

As required for an existing split, I ran the full dry run before changing any sandbox content:

`python3 /home/ubuntu/weil-launcher-nt/deliver.py Q159 prop-zl-smooth-proper-relative-purity --no-push`

I polled that same invocation to completion; it exited 1 with exactly one preflight failure:

```
units: sk-prop-smooth-proper-purity cites sk-thm-poincare-duality, which its nodes do not reach
```

Nothing was pushed. This confirms the maintainer-owned unit-route blocker from R1 persists on the current delivery base. Changing the unit's uses, statement or proof paragraphs exceeds the worker's permission to fill only realized and realized_by (brief section 0 and coord/dag-sync.md); adding an unused absolute-duality citation would undo R1. The repaired mathematics and source-error record remain ready for the next dry run after the maintainer installs the unit-route decision. This retry changes only this report; no Lean, compiler, direct git command, shared-project write, launcher write or agent dispatch was used.

## Dispatcher repair retry 4, 2026-10-18

I compared the retained item and unit against the current shared repository without git or shared writes. The item differs only in the worker-owned split fields; the unit differs only in realized and realized_by. The shared unit still cites sk-thm-poincare-duality and retains its separate absolute-duality alternative. Both helper ids remain absent from the shared DAG. Thus the maintainer metadata correction requested by R1 has still not reached the base.

I rechecked each requested repair in the actual JSON: step 8 is the elementary specialization of the relative result, with no uses; thm-weil-poincare-duality is absent from every proof step and proof_deps. The full source_error record contains the failing inference, nodal counterexample, identity-map test, source and replacement. Neither same-unit helper is declared as a tool use. All 23 citation quotations are verbatim substrings of the current cited statements, and their step/node pairs exactly cover the proof citations. Both helper nodes remain statement-only, and the longest proof step is 1109 characters. The 15 original search log records and all statements were retained; the search questions did not change.

As required, before changing this report I ran the full dry run and polled that same invocation until it exited 1. The only failure was:

```
units: sk-prop-smooth-proper-purity cites sk-thm-poincare-duality, which its nodes do not reach
```

The dry run printed PREFLIGHT FAILED, nothing pushed. This is the same maintainer-owned metadata blocker described in R1, not an unrepaired mathematical point. Brief section 0 permits only realized/realized_by edits to the unit, and coord/dag-sync.md requires authoritative maintainer route corrections followed by synchronization. I cannot repair this finding by altering the unit route, fabricating a dependency, or dropping truthful realization bindings. The retained proof and R2/minor repairs are ready to deliver once that authoritative correction is installed. No push, compiler, Lean edit, live-project or launcher write, or agent dispatch was performed.

## Dispatcher repair retry 5, 2026-10-18

I read the return and retained repair, compared every sandbox node and the unit with the current shared repository, and ran the required initial dry run before writing this entry. The item still differs only in blueprint, mathlib_searches, split_report, status, proof_deps, proof_origin and proof; the unit differs only in realized and realized_by. Both helper nodes remain absent from the shared repository and are statement-only obligations. I retained all proof text, sources, reports and the 15 recorded search results, whose questions have not changed.

R1 is repaired in the actual proof: step 8 only specializes the relative result, is elementary, and has no citations; neither its uses nor proof_deps includes thm-weil-poincare-duality. R2 is repaired in the actual node: split_report.source_error contains the precise failed lisse-lattice inference, nodal infinite-chain example, f=id test, valuation contradiction, source and replacement. The minor point is repaired: neither same-unit helper appears in split_report.tool_uses. I checked all 23 citation entries against the current cited statements and verified exact coverage of every proof-step/node pair. The longest step has 1109 characters. No mathematical or search question changed in this retry.

The single dry-run invocation was polled to completion (exit 1). It reported exactly one failure:

```
PREFLIGHT FAILED, nothing pushed.
units: sk-prop-smooth-proper-purity cites sk-thm-poincare-duality, which its nodes do not reach
```

This confirms that the maintainer metadata correction identified in the return and the previous retries is still absent. The old unit retains its independent absolute-duality alternative and cited unit, whereas the accepted repair must derive the absolute case from the relative argument. Brief section 0 allows only realized and realized_by changes, and coord/dag-sync.md reserves authoritative unit-binding/route maintenance to the maintainer. I cannot remove that route citation, restore the forbidden proof dependency, or clear truthful realization fields to bypass the check. The required next action is an authoritative maintainer unit-route decision and synchronization, then the normal dry run and delivery of this retained repair. No push, direct git command, shared repository or launcher write, Lean edit, compiler, or agent dispatch was performed.


## Dispatcher retained-repair verification, 2026-10-18

I resumed the existing sandbox and ran the required initial dry run before making any write. I compared all three node files and the unit against the current shared snapshot: both helper nodes remain absent there, the item differs only in its existing worker-owned split fields, and the unit differs only in realized and realized_by. The shared unit still cites sk-thm-poincare-duality and retains the old independent absolute-duality alternative. The authoritative maintainer correction identified in R1 is therefore still missing.

I checked the three return repairs in the actual item JSON. R1: step 8 is an elementary specialization of the relative result with no uses, and thm-weil-poincare-duality occurs in neither proof_deps nor any proof-step uses. R2: split_report.source_error contains the failed lisse-lattice inference, nodal infinite-chain counterexample, identity-map test, valuation obstruction, source position and replacement. Minor: neither same-unit helper is declared in split_report.tool_uses. I retained all statements, proof text, sources, reports and search records. I read the 15 existing command-log results rather than repeat unchanged search questions. All 23 citation records still exactly cover the proof-step/node pairs and quote verbatim substrings of the current cited statements. Both helpers remain statement-only; the maximum proof-step length is 1109 characters.

The sole invocation in this session was:

`python3 /home/ubuntu/weil-launcher-nt/deliver.py Q159 prop-zl-smooth-proper-relative-purity --no-push`

I polled the same process until exit 1. It reported exactly one failure:

```
PREFLIGHT FAILED, nothing pushed.
units: sk-prop-smooth-proper-purity cites sk-thm-poincare-duality, which its nodes do not reach
```

No second dry run or push was started. This finding cannot be repaired within the worker-owned fields: brief section 0 permits only realization-field edits in a unit, and coord/dag-sync.md requires a maintainer to install authoritative unit metadata corrections and synchronize them. Restoring the forbidden absolute-duality dependency would undo R1; suppressing truthful realization bindings would conceal the mismatch. The next action remains the maintainer's unit-route correction, followed by the required normal dry run and push. This verification changes only this report. No Lean, compiler, direct git command, shared-project or launcher write, or agent dispatch was used.


## Current dispatcher retry, 2026-10-18

The required initial dry run was polled as one invocation through exit 1. It again reported exactly one failure: `units: sk-prop-smooth-proper-purity cites sk-thm-poincare-duality, which its nodes do not reach`. Nothing was pushed. The current shared unit still has the old absolute-duality paragraph and citation; its sandbox copy differs only in realized and realized_by. The shared item remains imported, and neither helper node exists on that base.

I checked R1, R2 and the minor point in the actual JSON: step 8 has no uses and only specializes the relative proof; the forbidden absolute theorem is absent from proof_deps and all proof-step uses; source_error contains the failed inference, nodal counterexample, identity-map test, source and replacement; neither same-unit helper is a declared tool use. Both helpers remain statement-only. All 23 citation records quote current statements verbatim and exactly cover the proof citations. I read the 15 retained search-log results and retained them without rerunning unchanged questions. The proof steps remain below 2000 characters, with maximum 1109. No statement or mathematical route was changed in this retry.

The outstanding failure requires the authoritative maintainer unit-route correction specified by R1 and coord/dag-sync.md. Brief section 0 permits this worker only realization-field edits; restoring an unused absolute-duality dependency would reverse R1. The repaired split is retained for delivery after that base correction. This retry writes only this report and runs no compiler, Lean edit, direct git command, launcher/shared-repository write or agent dispatch.

## Latest retained-repair check, 2026-10-18

I ran the required initial dry run before writing this entry and polled its single process through exit 1. It reported exactly one failure: `units: sk-prop-smooth-proper-purity cites sk-thm-poincare-duality, which its nodes do not reach`. Preflight printed `PREFLIGHT FAILED, nothing pushed`; no push was attempted.

I compared all three retained nodes and the unit with the current shared repository. Both helper nodes remain absent there, the item differs only in its existing worker-owned split fields, and the unit differs only in realized and realized_by. The current shared unit still includes sk-thm-poincare-duality and the separate absolute-duality alternative. The required authoritative metadata correction has therefore not arrived.

R1 remains repaired: step 8 is an elementary specialization with empty uses, and thm-weil-poincare-duality appears in neither proof_deps nor any proof-step uses. R2 remains repaired in the actual split_report.source_error record, including the failed lattice inference, nodal infinite-chain counterexample, f=id test, valuation contradiction, source and replacement. The two same-unit helpers remain absent from split_report.tool_uses. I read both retained helper statements and the 15 existing command-log search results, retained their unchanged searches, and verified all 23 citation quotations against the current statements with exact step/node coverage. The maximum proof-step length remains 1109 characters. No statement or mathematical route was changed.

The remaining check requires the maintainer's unit-route decision identified explicitly in the return. Brief section 0 permits this worker only realized/realized_by changes in the unit, and coord/dag-sync.md reserves authoritative route metadata corrections to maintenance. Reintroducing the forbidden absolute-duality dependency would undo R1; altering realization bindings to hide the mismatch would misdescribe the split. The repaired files remain ready for the normal dry run and push after that base correction. This session changes only this report and runs no Lean/compiler/build tools, direct git commands, shared-repository or launcher writes, or agents.


## Retained repair revalidation (2026-10-18T02:32:15+00:00)

I resumed the sandbox, read the returned points and current stage-1 contract, and ran the required initial dry run before any write. Its single process was polled through exit 1. Server preflight reported exactly one failure: `units: sk-prop-smooth-proper-purity cites sk-thm-poincare-duality, which its nodes do not reach`. It printed `PREFLIGHT FAILED, nothing pushed`.

I compared all three node files with the current shared snapshot: the helpers remain absent there and the item changes only worker-owned split fields. The unit copy changes only realized and realized_by; the shared unit still requires the independent absolute-duality route. R1 remains repaired in the JSON: step 8 specializes the relative conclusion, is elementary, and has no dependencies; the absolute theorem is absent from all proof uses and proof_deps. R2 remains repaired in split_report.source_error with the false inference, nodal infinite-chain counterexample, f=id test, valuation obstruction and replacement route. Neither same-unit helper appears in split_report.tool_uses. I read both retained helper statements, the current blueprint proof and all 15 logged search results; their statements and search questions have not changed. All 23 citation entries are verbatim substrings of current cited statements and exactly cover the proof's step/node pairs. The longest step is 1109 characters.

The blocker explicitly identified by the return remains an authoritative maintainer unit-route correction, as coord/dag-sync.md explains. The worker may edit only realized/realized_by in the unit, so cannot remove its route citation; adding the forbidden theorem would undo R1. The repaired split is retained for normal dry run and delivery once that correction is synchronized. This retry changes only this sandbox report. No push, direct git command, live/shared/launcher write, Lean/compiler/build action or agent launch was performed.


## Dispatcher revalidation (2026-10-18T02:33:40+00:00)

The required initial dry run completed with exit 1 and exactly the same sole blocking finding: `units: sk-prop-smooth-proper-purity cites sk-thm-poincare-duality, which its nodes do not reach`. Nothing was pushed. Current shared metadata still has that citation; the sandbox unit differs only in realized/realized_by. I rechecked R1, R2, the minor tool-use repair, all 23 verbatim citation records and their complete step/node coverage. All remain repaired. The longest step remains 1109 characters. The authoritative unit-route correction reserved to maintenance by the return and coord/dag-sync.md has not arrived. No mathematical files were changed or searches repeated; the retained repairs remain ready for delivery after that correction.

## Latest required dry run, 2026-10-18

I ran the required single dry run against the current shared base and polled it to completion. It exited 1 with the sole preflight finding:

```
PREFLIGHT FAILED, nothing pushed.
units: sk-prop-smooth-proper-purity cites sk-thm-poincare-duality, which its nodes do not reach
```

The retained R1 repair still removes the absolute-duality alternative from the item proof: step 8 is an elementary specialization of the relative result, with empty `uses`, and `thm-weil-poincare-duality` is absent from `proof_deps`. R2 remains recorded in `split_report.source_error`, and the same-unit helper nodes remain ordinary proof dependencies rather than `tool_uses`. No statement, proof route, search record or node metadata was changed in this retry. The remaining failure is the maintainer-owned unit-route mismatch; this worker cannot alter the unit's `uses` or route under the stage-1 contract.


## Retained repair check, 2026-10-18T02:36:27.689101+00:00

I ran the required initial dry run before writing and polled its single process to exit 1. It printed PREFLIGHT FAILED, nothing pushed, with exactly one finding: `units: sk-prop-smooth-proper-purity cites sk-thm-poincare-duality, which its nodes do not reach`. No push was started.

I compared the retained node files and unit against current shared main without git. The helpers remain new; the item differs only in worker-owned split fields; the unit differs only in realized and realized_by. The authoritative unit still contains the independent absolute-duality alternative and its cited unit. R1 is repaired in the item: step 8 only specializes the relative result, and no proof citation or proof_deps entry uses thm-weil-poincare-duality. R2 is repaired in the actual split_report.source_error field, including the false lattice inference, nodal counterexample, identity morphism test and replacement argument. Both same-unit helpers are absent from tool_uses and remain statement-only. I read the 15 retained command-log search results without repeating unchanged queries. All 23 citation quotes remain verbatim in the current cited statements and exactly cover the proof citations. The maximum step length is 1109 characters.

The remaining finding is precisely the maintainer-owned route decision identified in R1. Brief section 0 allows only realized/realized_by edits in the unit; coord/dag-sync.md requires authoritative maintainer metadata repair followed by synchronization. Removing its uses/route or adding an unused forbidden theorem would violate that contract. The repaired split is retained for delivery after the authoritative correction. This session changes only this sandbox report and uses no Lean/compiler/build command, shared-project or launcher write, direct git command or additional agent.


## Current repair after authoritative unit correction (2026-10-18T02:39:13.071998+00:00)

The initial required dry run exited 1 with the previously recorded sole unit-reach finding and no push. During this retry the shared authoritative unit was corrected by maintenance: sk-thm-poincare-duality was removed from uses, the optional absolute-duality paragraph was removed from steps, and the absolute statement now just states the consequence. I refreshed the sandbox unit from this corrected base, then set only realized/realized_by for its five current paragraphs. Relative to current main this delivery changes only those two allowed unit fields. This resolves the metadata blocker without restoring the dependency forbidden by R1. The item split_report.blueprint now describes the current corrected unit rather than a pending maintenance request. Earlier blocked-run notes above are historical.

R1 remains repaired: step 8 is an elementary specialization of step 7, has empty uses, and thm-weil-poincare-duality appears in no proof dependency. R2 remains repaired in the actual split_report.source_error record, with the failing lattice inference, nodal infinite-chain example, f=id and the valuation obstruction, as well as the replacement argument. The minor repair remains: neither same-unit helper occurs in tool_uses. I reopened all three retained node files and the current blueprint proof, compared the item against current shared main, and verified all 23 citation entries are exact substrings of the current statements and cover precisely every proof citation. The helpers are still new, statement-only and unsplit; no theorem or search question changed. The 15 retained logged searches are reused. The longest proof step is 1109 characters and contains no newly hidden lemma. The source/hypothesis/small-case review above remains applicable.

No live/shared/launcher file was written, no direct git command or Lean/compiler/Lake tool was run, and no agent was started. Server dry-run and push results follow after completion.

The final dry run completed with exit 0: `OK (not pushed) deliver/Q159/prop-zl-smooth-proper-relative-purity at f3f7966148: preflight passed`. The transient duplicate-request rejection cleared before this admitted run; no overlapping delivery was started. The corrected unit now passes the unit-reach check. The normal push will rerun preflight on this report update.
