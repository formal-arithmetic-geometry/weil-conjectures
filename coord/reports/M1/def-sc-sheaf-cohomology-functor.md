1. Files written

- `dag/nodes/sec-picard-framework/def-sc-sheaf-cohomology-functor.json`: item, statement, Mathlib searches already recorded as no match; status set to `split`.
- `dag/nodes/sec-picard-framework/lem-sc-global-sections-left-exact.json`: statement-only node, no Mathlib match.
- `citations.json`: three verbatim step-1 citations.

2. Attachments

None.

3. WANTED:

None.

4. What was wrong

The imported item cited `def-sc-ext-sheaf` for the meaning of sheaf cohomology, but that node defines Ext and is not the cohomology definition. I corrected the item to use the scheme-module category, global sections, enough injectives, and right derived functors. The source is Stacks Project Cohomology Section 01DZ (`cohomology.tex`, section label `section-cohomology-sheaves`), whose ringed-space clause defines $H^i(X,\\mathcal F)$ by an injective resolution and states that the family is a universal delta-functor. The blueprint ancestry is `thm-sc-p1-duality`, proof Step 2.

5. What could not be finished

No Lean declaration with the item tag or exact statement was present in either source checkout. No Mathlib declaration states the scheme-module global-sections fact or the complete cohomology functor statement, so the item remains a natural-language DAG node.

## Review by M1

I read the item JSON, `sk-thm-picard-duality`, `sec-picard-framework`, the source text for Stacks Tag 01DZ, and the source statements of every cited node. The new `lem-sc-global-sections-left-exact` statement was checked against Stacks Lemma 01EZ's setup: evaluation at $X$ is additive and preserves kernels. The enough-injectives statement was checked in `lem-weil-pbc-scheme-modules-enough-injectives`, which explicitly gives an injective embedding for every module. The generic right-derived-functor node states that the $R^n v$ form a delta-functor; its definition of delta-functor includes additive functors, so it supplies the induced maps and composition law used in step 1. The step is therefore non-elementary and cites all three statements; only the final inference that a functor preserves composition is elementary.

I searched the whole DAG and blueprint for an existing global-sections-left-exact statement and for the item tag; no duplicate or exact blueprint node was found. Mathlib searches for the new node covered LeanSearch, Loogle, and source grep and found no exact match. I tested the corrected definition on the empty scheme and on $X=\\operatorname{Spec}(k)$: global sections are respectively the zero functor and the identity on $k$-modules, and the functoriality/composition equations reduce to the corresponding identities. No source text was silently weakened; the only correction was removing the unrelated Ext dependency.
