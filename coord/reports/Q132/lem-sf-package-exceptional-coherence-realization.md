# Stage-1 worker report

Item: lem-sf-package-exceptional-coherence-realization. Group: Q132. Date: 2026-10-21.

## Files written

- dag/nodes/sec-six-functors/lem-sf-package-exceptional-coherence-realization.json: statement; split into nine proof steps. No Mathlib match for the assembled geometric exceptional/coherence theorem.
- citations.json: 26 step/node entries, each with a verbatim substring of the cited node's statement.
- report.md: this report. searches.jsonl is the unedited search-command log.

New nodes: 0. New Mathlib leaves: 0. No unit record changed: the item is a created prerequisite of prop-functor-package, not the unit's key node.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint id and exceptional/coherence notions found no declaration stating the entire item. The existing ambient-adjoint and composition interfaces concern parts or conditional variants; they do not attach the unconditional theorem at all four stages.

## WANTED

None. The source used is already present. No SGA source is used.

## Findings and changes

The original statement is retained verbatim. Its proof was empty. Added its dimension-definition dependency and a complete argument using existing nodes; retained provenance and the inherited Mathlib search records. The ancestor search identifies prop-functor-package. Whole-blueprint searches for the item title and exceptional adjunction found no other node stating this combined item. The ancestor is deliberately not a proof dependency. No newly coined lemma or restatement of a clause is needed.

A potential C4 error was avoided: fix-prop-adjunctions now makes its exceptional clause conditional on exceptionally admissible f. It cannot discharge this unconditional item. Step 3 instead uses the class-relative adjunction and the independent preservation theorems. Another potential domain error was repaired before delivery: the item assumes uniformly bounded cohomology of integral reductions, not an additional uniform Tor condition. Step 5 explicitly cites lem-coef-integral-residue-tor to obtain the uniform Tor interval before invoking integral exceptional reconstruction. At algebraically closed coefficients, the rational-operations statement alone is insufficient: step 7 also uses thm-coef-qbar-verdier and the common-stage category definition.

Mathlib searches: the new logged LeanFinder searches in two phrasings returned ordinary sheaf pullback/pushforward, condensed functors, local cohomology and generic adjunctions, not constructible exceptional adjunctions or the coefficient coherence package. LeanSearch likewise returned ordinary sheaf and over-category adjunctions. The grep hits for Verdier concern triangulated localization and historical references, not sheaf Verdier duality. The first Loogle query contained the unknown identifier CategoryTheory.NatIso; this is recorded as an invalid query, not absence. The corrected CategoryTheory.Adjunction query returned the generic adjunction definition and constructors. None has the geometric operations and coefficient comparisons of this item. All appended queries and result summaries come from searches.jsonl; no search was invented.

## Not duplicates

There are no new nodes and therefore no new/existing same-tag pairs. The existing finite, integral, rational, algebraically closed and coherence nodes are reused. In particular, no finite-stage formula, coefficient-passage theorem, compactification lemma or elementary common-stage equation was created again.

## Review by Q132

I read the worker contract, stage-1 rules, three-level route rules in SETUP.md, GOAL.md, the chapter and unit records, and delivery-errors B--E (including their merged copy). I read the actual main-20261015 prop-functor-package proof, especially its exceptional-adjunction and final coherence sentences, and the finite-exceptional, integral-exceptional, rational-operations, qbar-Verdier and coherence statements at that snapshot, including the coherence proof. Those sentences prescribe exactly the coefficient-passage and coherence route followed here. The blueprint is agent-written, so proof_origin.by is agent. The current DAG statements supply corrected precise domains and empty-scheme conventions. There are no new-node sources to audit.

For step 1, I opened def-weil-finite-type-morphism, lem-pc-separated-quasi-separated, lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-qcqs-morphism-permanence and prop-nagata-compactification-category. Finite type gives quasi-compactness by evaluating over the whole affine base Spec k. The separated structure morphism gives relative quasi-separatedness; permanence with the quasi-separated affine base gives absolute quasi-separatedness of Y. Thus the compactification-category theorem's qcqs base assumption is established before invoking nonemptiness. Its objects explicitly have quasi-compact open j and proper p.

For step 2, def-weil-proper-morphism includes finite type, and lem-sfb-finite-type-composition-base-change explicitly proves finite-type composition; it is a Mathlib leaf, not an uncited algebraic-geometry assertion. Lem-kun-dimension-finite-type then applies to the compactification as well as X and Y. The dimension definition explicitly assigns minus infinity to the empty space, so choosing bound zero in that case and a nonnegative bound otherwise is valid. No maximum over an empty cover is used.

For step 3, thm-sf-ambient-adjoint-class explicitly supplies the natural bounded-below Hom bijections for etale-origin K and says bounded constructible inputs qualify. Its bound is available from step 2. The defining formula in def-weil-exceptional-inverse-image identifies its R_c with the operation used in the item; no theorem was inferred merely from the definition. Lem-trf-open-ctf proves the preservation of j_!, and cor-sf-direct-image-ctf-proetale proves the preservation of Rp_* with source dimension bounded by d. Thm-sf-preservation-class explicitly proves finite exceptional preservation with separated target Y, which is an assumption of this item. These statements justify restricting both functors and the Hom bijections to full finite-Tor subcategories. Restriction retains the same unit, counit and their equations. This does not assume a right adjoint on arbitrary pro-etale objects.

For step 4, lem-coef-finite-exceptional says precisely the dual-pullback-dual formula, quotient cocycle and the two displayed unit/counit equations used in the step. The finite-Tor domain and positive indices were already checked. At m=n its identity normalization agrees with the stated identity comparison; n=1 is included.

For step 5, lem-coef-integral-residue-tor applies because ell is invertible on Y and the integral input is derived complete with bounded residue cohomology. It supplies one finite-level Tor interval for all n, without identifying constructibility with site-perfectness. Prop-coef-integral-exceptional-adjoint specifies the coherent realization before the inverse limit, its constructible adjunction, completed-pullback formula, all finite reductions and compatibility of units and counits. It states the uniform output interval using the nonnegative dimension bounds already obtained. This resolves the actual integral domain rather than introducing an extra input hypothesis.

For step 6, lem-coef-rational-operations explicitly asserts the rational adjunction and formula and preservation of evaluations, units and counits, including finite scalar extension. Its completed integral tensor convention is kept. For step 7, thm-coef-qbar-verdier gives the common-stage internal-Hom identification, constructible adjunction and formula. Def-weil-algebraically-closed-coefficients says arrows, their equality and composition are represented over finite common fields. Thus the unit/counit/evaluation normalization follows by representing them at one common field and using step 6's scalar compatibility; equality of their classes and triangle identities follow from equality at that field. No unsupported limit-of-categories assertion is inserted, and no reduction functor is applied to a field object.

For step 8, I opened each of lem-fix-operation-reduction, thm-coef-finite-hom, lem-coef-integral-hom-reduction and lem-coef-integral-finite-extension. The first explicitly preserves the structural evaluations and adjunction maps but only gives its elementary finite Hom comparison for a site-perfect first variable. The second explicitly removes that restriction on the finite-Tor constructible domain and characterizes its comparison by evaluation. The third says its reduction comparison preserves evaluation and transposes, and the fourth gives the same evaluation normalization for finite coefficient-field extension. These are actual statement clauses, not facts taken from their proofs. They justify the evaluation assertions for general variables on precisely the stated domains.

For step 9, fix-prop-coherence explicitly states the four coherence types, extra smooth-orientation/site-perfect pairing compatibilities and field Weil equivariance. It applies to the same operation datum and the already proved comparisons. Restricting each equation to the intersection of its domains simply restricts equal natural transformations. The item assumes finite-field descent and Weil structures where equivariance is asserted; it does not assert arbitrary-base-change commutation of Verdier duality. The ordinary and exceptional coefficient maps are the normalized ones checked in the preceding steps.

Against B--E: no new statement-only node contains a hidden proof, no elementary fact became a node, no clause was moved into a new restatement, and no Mathlib leaf was manufactured. Every uses entry has its cited statement open and a verbatim quote in citations.json. I checked that the dependency closure of each substantive cited theorem does not return to the item. The source route and the statement have not changed. Generic off-unit tools are declared in split_report.tool_uses, not in a top-level approval field. Each step is shorter than 2000 characters; there is no long step concealing a separate lemma. Edge cases checked are empty X or Y, zero objects, f=id, n=1, identity quotients, identity finite-field extension, and enlargement of the common finite field. All formulas remain typed and use the supplied identity/triangle/cocycle laws. There is no STATEMENT-DISPUTED finding.

## Unfinished work

None in the stage-1 split. Independent maintainer review remains part of the delivery process.

Dry-run repair: expanded three verbatim citation excerpts to include the relevant hypotheses or full formula; the citation gate requires at least 40 characters unless quoting the whole statement. No mathematical change was needed.
