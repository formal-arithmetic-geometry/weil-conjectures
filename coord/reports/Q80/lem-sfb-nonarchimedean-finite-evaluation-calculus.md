# Worker report — Q80

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-nonarchimedean-finite-evaluation-calculus.json: existing statement, now split in six proof steps; no statement or statement-dependency change.
- citations.json: verbatim statement quotations for both proof citations.
- searches.jsonl: actual msearch.py search receipts; original item search records retained in the node, new searches appended.
- baseline.json: sandbox-only original live node for comparison.
- report.md: this report.

Zero new nodes and zero new Mathlib leaves. The initial sandbox contained only dispatcher brief markers, no earlier node, report, citations or search log. No delivery command was active or interrupted in this session. All writes are confined to the designated sandbox. No Git command, Lean writing, compilation, Lake/build command, agent delegation or launcher modification was performed.

## Attachments

None. Searched the entire WeilConjectures source for the exact blueprint tag, nonarchimedean, finite evaluation and related terms. The scalar field norm material supplies only ingredients. The neighboring Sheaf/RepresentationTheory/BoundedFiniteEvaluationRectangleReplacement.lean declaration at line 99 is sorried at line 139, and in any event concerns the parent, not this entire statement. It cannot finish the item.

## WANTED

No additional document is needed for this split. The item is an agent-formulated auxiliary assertion: the source paragraph does not itself state it. Its elementary proof is supplied honestly as agent-written, using the existing Mathlib extreme-value node as the only topological theorem.

## What was wrong and what changed

The imported auxiliary node had a complete statement but no proof. Its source is main-20261015's direct-images proof paragraph (3), read in full together with chapter and unit records. That paragraph gives proper/open direct-image preservation and compactification, not a finite-evaluation theorem. I also read the retained Q76 report's original proof steps 12–14, which contain the expansion, coefficient bound, compact supremum, coefficient-subspace and parameter arguments allocated to this item. The six steps now supply these arguments with explicit continuity estimates, induction and pointwise formulas. No SGA source is used.

I initially considered a new Mathlib leaf for compact supremum norms. A whole-DAG search found lem-sfb-compact-real-function-minimum, whose statement is enough: apply it to minus the norm and get an attained upper bound. This is a few-line specialization, so a new node would violate the elementary/duplicate rule. I discarded that plan before creating a node. lem-sfb-compact-function-space-complete assumes a Hausdorff domain and complete target, so I did not cite it: those hypotheses are unavailable here. The existing minimum theorem has precisely the weaker topology hypotheses needed.

The source statement remains verbatim, including arbitrary compact domains, arbitrary parameter spaces, incomplete targets, nonclosed coefficient subspaces, zero coefficients and empty lists. No STATEMENT-DISPUTED issue was found. Unit/chapter records and all unrelated nodes are unchanged. The existing null blueprint.from.node is retained because tools/blueprint_refs.py ancestor reports None through the inherited created.item chain; its precise auxiliary place was already filled. Whole-blueprint searches for ultrametric/nonarchimedean, supremum norm, continuous functions, finite evaluation, minimum and supremum found no blueprint equivalent. Potential string matches concern unrelated schemes or coefficient sheaves, not this analytic statement. blueprint.same_as remains an empty list.

## Mathlib searches and source reading

I read every new msearch.py hit and its logged summary. Searches include all four prescribed kinds and two mathematical phrasings for the full item. LeanFinder returned generic finite-dimensional linear-map continuity and Hom/series constructions. Loogle's ContinuousMap, NormedSpace query returned ContinuousMap.normedSpace and BoundedContinuousFunction.compContinuousCLM; I read Compact.lean around lines 155–239 and Bounded/Normed.lean around its precomposition declarations at 302–321. These give ingredients, not the combined statement by one-line specialization. LeanSearch additionally returned ultrametric finite-sum bounds. That bound is a direct induction from the explicit hypothesis here, written in step 3; it is not extracted into another node.

Candidate supremum searches returned ContinuousMap.norm_le, norm_coe_le_norm and norm_eq_iSup_norm. I read their hypotheses and declarations at Compact.lean:39,199,207,234; no completeness or Hausdorffness is needed. They confirmed the approach, but the existing minimum node makes a new leaf unnecessary. I read its actual source IsCompact.exists_isMinOn at Mathlib/Topology/Order/Compact.lean:230–235 and its full DAG statement, which explicitly allows an arbitrary topological domain. No non-elementary Mathlib fact is used merely by citing the search result: the proof uses the existing minimum node.

One grep invoked the wrapper on a file rather than a directory, causing malformed file/line output; it was repeated on Topology/ContinuousMap and the actual file was read. Its honest verdict identifies this rather than claiming a verified location. Loogle Continuous.sum returned an unknown-identifier diagnostic, recorded as a rejected query and not evidence of absence. All recorded new queries are actual entries in searches.jsonl; no service failure is presented as an empty successful search. The original Q76 search metadata is retained as inherited history, not claimed to have been rerun by Q80.

## Not duplicates

No new node is created. The proposed compact-supremum helper was omitted because lem-sfb-compact-real-function-minimum already yields it by applying the minimum assertion to minus the norm. The whole DAG and blueprint were searched before this decision. No same-Stacks-tag pairs arise; no new Stacks citation is introduced, since the relevant analytic leaf's source is Mathlib itself.

## Review by Q80

I read delivery-errors sections B–E in both the original and merged checklist, the item and its source paragraph, the Q76 allocation of original steps 12–14, the unit/chapter route and the full statements of both cited nodes. This review concerns what the steps actually use, rather than accepting an id or a source name as a proof.

Step 1 uses only the norm and vector-space axioms stated in the item. Its displayed Lipschitz estimate for fixed scalar multiplication and ultrametric estimate for addition prove the continuity it needs; the finite-list induction constructs a continuous result. Linearity is finite distributivity over the commutative scalar field. No generic continuity theorem is silently imported and no completeness is involved.

Step 2 cites lem-sfb-compact-real-function-minimum for exactly its assertion that a continuous real function on a nonempty compact subset attains a minimum. I verified the statement and Mathlib source: it requires no separation of the source or completeness of V. Here T is respectively X and Y, C is the whole T, compactness and nonemptiness are hypotheses of the item, and continuity of minus the norm follows from the displayed reverse triangle inequality. A minimum of minus the norm is an attained upper bound for the norm, so its value is exactly the finite supremum. The citation does not claim the existing complete-function-space node applies to an incomplete target.

Step 3 starts with the nonnegative number B times the finite supremum from step 2. Each summand has norm at most this number by exact scalar homogeneity. The empty sum is the induction base and the given max inequality is the induction step. Taking a supremum of those pointwise bounds is the definition of supremum, not a missing operator-norm theorem. A linear subspace contains zero and finite linear combinations by definition; the proof uses no limit or closedness assertion. In particular B=0, all-zero coefficients and the empty list are covered.

Step 4 verifies continuity of the parameter-coordinate substitution on basic product opens, then applies exactly step 1's finite operations. S need not be compact, nonempty, Hausdorff or metrizable: no supremum is taken over S. Each fixed-s slice is continuous by the product inclusion, and substitution into the displayed formula is literal equality. Identities on slices give identities at every pair (s,y) by function extensionality. Empty S has the unique family.

Step 5 expands the composite as the actual double sum, with coefficient order mu_k lambda_j and coordinate b_j composed with c_k. These domains and codomains match Y to X and Z to Y. Composition preserves continuity by the inverse-image definition, and the pair of finite index sets is finite. Precomposition has the same argument and coefficients. No choice of maps or coefficients depends on V. Empty index sets do not require choosing a maximum of an empty set, and their double sums are zero.

Step 6 cites def-weil-l-adic-numbers for precisely its explicit valuation and absolute-value formula on rational numbers. For k nonzero the exponent of ell in the integer k is nonnegative; coprimality makes the exponent in m zero, and m positive ensures its denominator is nonzero. Thus k/m has norm at most one; k=0 is handled separately. The earlier steps apply with B=1. The singleton domain and V=0 are direct evaluations, and no completeness is added. citations.json quotes a verbatim passage from each cited node's statement for the actual step using it.

Every non-elementary input is the cited minimum theorem; all other claims have the elementary arguments written explicitly. Each step is between 417 and 552 characters, so no step passes the long-step threshold or hides an independently stated lemma. No new node restates a clause of the item and no dependency can cycle back through the item: the minimum node and the coefficient definition are existing Mathlib leaves. Both lie on the allowed route or are Mathlib tools; no off-unit non-leaf tool use is introduced.

## What could not be finished

Nothing remains mathematically unresolved for this stage-1 split. Validation and push receipts are reported by the required delivery command; no receipt is claimed before it is printed.
