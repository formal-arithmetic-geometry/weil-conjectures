# Stage-1 report: lem-pur-system-clopen-mate-identification

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-system-clopen-mate-identification.json: statement, split in four steps; Mathlib has generic mate calculus but no match for this identification of specified strict-system arrows.
- citations.json: eight step/node entries, each quoting the cited statement verbatim.
- searches.jsonl: six searches actually run with msearch.py, including a second semantic phrasing and source grep for the mate candidate.
- report.md: this report.

No new nodes; no new Mathlib leaves. No Lean files or compiler tools were used. All writes were in the assigned sandbox. The original statement, statement dependencies, inherited search records and blueprint ancestry were retained.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for clopen/mate and proper/open/system terminology, including its SixFunctors directory. No project declaration states the item. The Sheaf presentation named by the definition dependency is not evidence that this new identification theorem is proved.

## WANTED

None. I read the local Stacks sources and current blueprint rather than assuming the strict-system comparison was quoted from Stacks.

## Issues found and resolved

The item was unsplit, with no prior sandbox proof or report and no released repair note for this item. The principal risk was to confuse fixed-ring strict towers with varying-ring systems, or to infer derived equality from finite evaluations. The proof now uses the explicit n to n-1 reindexing of lem-pur-system-tensor-presentation-identification, its operation comparisons, and actual ordinary section maps before localization. The constant-ring tower theorem in the statement supplies geometric context; I do not specialize its fixed-ring assertions to a varying coefficient ring.

A whole-DAG search located lem-sf-ambient-exact-clopen-comparison-localization, whose statement already supplies the simultaneous exact-localization and restriction-normalization comparison in both finite and semilinear categories. It is reused, not recreated. For Gamma the proof uses lem-sf-semilinear-proper-open-mate-pasting, whose statement explicitly identifies the proper mate with the open adjunct of lambda inverse; this avoids applying the integral realization theorem's bounded normalized-input restrictions to arbitrary systems. No statement correction or route departure was needed.

## Unfinished work

None for this one-level split. Existing unsplit dependencies remain their own stage-1 items. The required dry run and delivery are recorded below when completed.

## Not duplicates

No new node is proposed. The existing ambient exact-localization theorem subsumes the geometric localization portion of this item and is cited in Step 3. The existing tensor-presentation theorem supplies reindexing and operation comparisons in Step 1, while the existing semilinear mate-pasting theorem supplies the intrinsic Gamma characterization in Step 4. Blueprint searches for clopen, proper open, and system clopen found no imported node stating this entire identification; same_as remains empty. I checked the existing nodes' statements and dependency closures before citing them; none reaches this item.

## Mathlib searches

All six new entries were run through the required msearch.py command and the actual results were read. LeanSearch returned Scheme.Modules.restrictAdjunction and open/closed coercion results, which concern different categories and do not identify our clopen arrow. The first LeanFinder query returned locally constant sheaf and gluing statements. The second phrasing returned open-set adjunction identities, general mate identities, and basis sheaf extension. Loogle found CategoryTheory.mateEquiv and its compatibility formulas. The geometric grep in CategoryTheory returned zero hits, and the second grep found Mathlib/CategoryTheory/Adjunction/Mates.lean:84. I read its definition and unit/transformation/counit word: it covers the generic last calculation, but supplies neither the quotient-system presentation nor the concrete geometric normalization, so the item is not a one-line Mathlib specialization. The original item's historical searches were preserved as inherited records, not claimed as freshly run by Q79.

## Review by Q79

I read Stacks more-etale.tex Tag 0F7B (lemma-shriek-proper-and-open), including its canonical map construction, and sites-cohomology.tex Tag 07A7 (remark-base-change), which constructs a map by taking the adjunct of the pulled-back counit. The former is an etale comparison theorem, not a strict semilinear presentation theorem; neither source alone proves this item. I therefore marked the proof as agent-written and cited existing DAG statements for every additional comparison. I read the main-20261015 ancestor proof's final coherence sentence and its live parent split: this item realizes the former Step 2 identifying the clopen/mate factors of the system tensor interchange. The unit remains sk-thm-sf-compatibility, using the coefficient, projection-formula and mate route already assigned to it. There are no new nodes whose source needs separate review.

For Step 1 I read the complete statement of lem-pur-system-tensor-presentation-identification. It has exactly the same quotient rings, small pro-etale representatives, unbounded systems, and n>=1 indexing; it explicitly sends n to n-1 and preserves sections and transitions, adjunction units/counits, open units and compositors. Thus I can compare the two ordinary projectors by their actual identity/zero section formula. I wrote the transition compatibility: both identity and zero commute with each semilinear transition. Termwise extension and localization of an already equal transformation preserve equality; this is distinct from claiming derived evaluations detect maps.

For Step 2 I read lem-sf-open-tensor-normalization and lem-sf-proper-open-projection-mate in full, including their strict-system clauses. The former gives the inverse-beta adjunct and fixes its open unit, not merely the existence of some isomorphism. The latter defines alpha using that same beta, the clopen projector and the canonical final compositor, and explicitly includes ringed diagram systems. Replacing those factors by the equal factors from Step 1 gives the displayed a. This is elementary substitution into an existing composite, so Step 2 is marked elementary; it is not an invocation of an uncited base-change existence fact. I verified bs=k_1 and qs=r give the required composition identifications with the correct direction.

For Step 3 I read lem-sf-ambient-exact-clopen-comparison-localization and def-pur-system-tensor-mate-arrows. The former includes the semilinear category, arbitrary unbounded complexes, ordinary restriction identity with uniqueness, the localized specified beta, and the exact clopen composite. Its hypotheses allow nonseparated finite-type schemes and hence apply to our separated ones. Both proper maps and both quasi-compact open maps are present, as is p_1 k_1 = i r; no Cartesian square is required. The latter definition specifies the unsuppressed open-unit restriction formula and its unique ordinary arrow. I explicitly expanded the restriction identity as u_k composed with r*(u_i inverse) composed with theta, before using uniqueness. This distinguishes uniqueness of the ordinary arrow from any unsupported faithfulness statement on derived morphisms.

For Step 4 I read lem-sf-semilinear-proper-open-mate-pasting, lem-sf-proper-open-projection-mate, and def-weil-pbc-adjunction-mate. The first allows an arbitrary ring sequence and precisely the same proper/open square, with no normalized-input assumption, and identifies its proper mate with the open adjunct of lambda inverse. This matches the intrinsic Gamma referred to in the second node's system clause. The definition gives the exact component formula; I substituted all six functors explicitly to obtain the requested gamma, with proper counit for r and proper unit for p_1 in the required order. The statement's square identification is retained throughout. No projection-formula identity is used to prove its own normalization, and no result is taken from another node's proof instead of its statement.

I checked delivery-errors B through E against the files. There are no new statement-only node formatting, missing-source or artificial-leaf issues. Every cited statement has a verbatim quote in citations.json, and every non-elementary input is a cited existing node. The proof does not introduce a node restating a clause. All four proof steps are below 2000 characters, and I checked that none hides an uncited comparison. A dependency-closure traversal found no path from the cited normalization/localization/presentation nodes back to the item.

I tested the formulas on the empty selected open (projector and a are zero), the Cartesian case (s is identity and a=beta), a disjoint extra clopen component (projector is (1,0)), a refinement with r=id (projection to the selected section), and identity maps (canonical units and compositors give identity). For nonflat quotient transitions, e.g. R/t^2 to R/t, the projector still commutes with the semilinear transition because it is identity or zero, and no exactness of coefficient reduction is used. Arbitrary unbounded and noncartesian systems cause no additional step: the cited localization and mate statements are already on their whole ordinary derived categories. The proof asserts equality of maps, not invertibility of gamma.

## Validation

The required deliver.py --no-push invocation exited 0 and printed `OK (not pushed)` at 169c175acf9 with preflight passed. The direct-delivery brief authorizes Q79 to push after this self-review and successful dry run.
