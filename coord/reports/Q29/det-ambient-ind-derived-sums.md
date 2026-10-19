# Stage-1 worker report: det-ambient-ind-derived-sums

## Files written

- `dag/nodes/sec-six-functors-basics/det-ambient-ind-derived-sums.json`: item, split; no complete Mathlib match.
- `citations.json`: literal verbatim statement excerpts for all eleven citations in the six proof steps.
- `report.md`: worker review and handoff.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches in the read-only slopmaster2 `WeilConjectures/` for the exact blueprint id/tag, ind-constructible terminology, ambient-ind-derived terminology, and coproduct/cohomology terminology found no declaration proving all three clauses. General module-sheaf Grothendieck results are inputs, not attachments of this item. Upstream master is reference material only.

## WANTED

None.

## Corrections

The statement now introduces X, the fixed prime and finite coefficient extension, the actual condensed coefficient rings, their pulled-back module category, IndCons, Dic, small families, and canonical truncations. The three conclusions are unchanged. In particular the Qbar coefficient is the ring of `sk-def-sfb-qlbar-condensed`, not the full continuous-function condensed ring. No completeness or geometric finiteness assumption has been added.

The imported proof's reference to `sk-prop-ind-heart` is replaced by the existing precise sum-closure statement `det-ind-heart-filtered-colimits`. Exact sums alone do not establish the coproduct universal property after localization; step 2 instead cites the existing termwise-derived-coproduct theorem. The lower-truncation computation is elementary and stays in step 4 rather than becoming a new node.

I repaired two inherited citation excerpts to preserve the actual whitespace of the constructible-local-model statement; they are now literal substrings, not merely whitespace-normalized quotations. I also corrected the inherited report's obsolete assertion that chapter/unit metadata and records were missing: the current shared item has chapter `sec-six-functors-basics` and unit `sk-cor-ambient-ind-derived`, and both records were read. The sandbox copy includes those unchanged metadata values; no maintainer-owned field is changed by this delivery. This detail node is not the unit's key statement, so no unit realization file is delivered.

## Not duplicates

No new nodes. Existing general module direct-sum nodes over an ordinary scalar ring are not silently identified with this coefficient category. The existing condensed-coefficient ambient-coproduct node supplies exactly the required assertion. Whole-DAG and blueprint searches for IndCons, ambient derived categories, sums and truncations locate the already-cited ind-heart, triangulated and localizing nodes. None other than this item states its conjunction of the three clauses.

## Review by Q29

I read delivery-errors B--E, the three levels of SETUP, GOAL, dag-sync, the chapter and unit JSON records, and the main-20261015 chapter, unit statement/proof, and item statement/proof. The six steps realize the unit's prescribed route: exact sums and cohomology, truncations, then the localizing inclusion. No SGA source is used. No new node requires a separate source or duplicate comparison.

For step 1, `sk-def-sfb-module-objects` gives actions in ordinary abelian sheaves, and `sk-def-sfb-sheaf-tensor` describes their tensor as sheafification of the sectionwise tensor. Its universal property identifies these actions and linear morphisms with usual sheaves of modules over the ring sheaf Lambda_X. I read the entire statement of `lem-weil-pbc-ring-sheaves-grothendieck`: it applies to an arbitrary ring sheaf on a small site in the fixed universe and states exact filtered colimits. Stacks 03DB, `sites-modules.tex`, `lemma-limits-colimits`, explicitly gives that exactness. The finite-subset filtered-colimit formula for a sum and finite biproduct exactness prove exactness of all small sums directly. This is elementary relative to the cited inputs, not an appeal to flatness or a theorem for constant coefficients.

For step 2, clause (1) of `det-def-localizing-closure-existence` states termwise computation of arbitrary small coproducts in precisely the unbounded module-object derived category used here. Stacks 07D9, `injectives.tex`, `lemma-derived-products`, states and proves this for any Grothendieck abelian category using K-injectives. The two displayed short exact sequences in the step then compute cycles, boundaries and cohomology after summing. The comparison is induced by the coprojections. No boundedness or common lower bound is used.

For step 3, the final sentence of `det-ind-heart-filtered-colimits` explicitly says arbitrary direct sums of ind-constructible sheaves are ind-constructible, for E and Qbar. It is stronger than a mere definition or a filtered-colimit-only assertion, and together with step 2 proves the claimed closure of Dic.

For step 4, `lem-weil-pbc-truncation-cohomology` supplies the upper-truncation cohomology formula for any abelian category. I read Stacks 0118, `homology.tex`, `section-truncations`, including the canonical cochain constructions. The lower-truncation formula is written out using the cokernel in degree n: its cycles are ker(d^n)/im(d^(n-1)), its next boundaries are im(d^n), and the other degrees are unchanged or zero. These computations respect maps and hence quasi-isomorphisms. The zero finite local model in `sk-def-sfb-constructible` makes zero constructible; its singleton filtered diagram makes it ind-constructible. Thus both truncations satisfy the inline Dic predicate.

For step 5, `sk-def-sfb-bounded-constructible` states that every cohomology sheaf is constructible. The step uses this defining clause, not the node's extra triangulated assertion, which requires topological Noetherianity. The singleton filtered diagram gives ind-constructibility, with the zero model again supplied by `sk-def-sfb-constructible`. Thus the step imposes no Noetherian or completeness assumption.

For step 6, `det-ambient-ind-derived-triangulated` states the full triangulated and isomorphism closure of Dic. Steps 3 and 5 supply sum closure and containment of Dbc. Clause (2) of `det-def-localizing-closure-existence` applies to any class of objects S, so its actual intersection/minimality statement applies to S=Dbc and proves the inclusion. It does not need a small category of bounded constructible objects, or identify Dbc with Dctf. The two generic off-unit tools and their purposes are declared in `split_report.tool_uses`; no unit step has been replaced by a different route.

I checked the empty family, singleton family, zero complex, an unbounded family with no common bound, complexes concentrated at n and n-1, and a nonzero differential across the truncation boundary. The kernel/cokernel truncations give the stated degrees in each case. The localizing argument claims only inclusion; it makes no claim that Loc(Dbc) is truncation-stable. All cited statements were reopened, all eleven citation excerpts are literal substrings of them, and `proof_deps` is exactly the union of step `uses`.

The Mathlib searches retained in the node are logged queries made through msearch.py. I repeated the full-item LeanFinder, the alternate general Serre-subcategory LeanSearch phrasing, Loogle `"IndConstructible"`, and the source grep, and read the returned types. The results concern generic derived categories, generic triangulated closures and ordinary/light condensed module categories; none gives the full geometric statement. No unavailable service is represented as a negative result. No Lean file is written or compiled.

## Validation

The earlier attempt timed out waiting for a shared worktree slot before preflight began. This retry uses the same authorized command, `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q29 det-ambient-ind-derived-sums --no-push`, with its output in `dry-run.log`. No launcher modification, resource-limit bypass or push is performed. The final handoff is READY only after this command prints OK.

The retry reached preflight and printed `OK (not pushed) deliver/Q29/det-ambient-ind-derived-sums at cb65423278: preflight passed`. A final rerun covers the refreshed report and literal citation excerpts; its complete result is retained in `dry-run.log`. The dependency traversal found no path back to this item across 2,357 dependencies. It also found the inherited downstream missing id `def-weil-pbc-etale-morphism`, so this local traversal is not represented as a globally green DAG check; the delivery preflight judges the overlay against its baseline.

## Second reading by Q29

I independently opened the current main-20261015 chapter, unit, item statement/proof, all statement and proof dependencies, and Stacks `sites-modules.tex` Tag 03DB (`lemma-limits-colimits`), `injectives.tex` Tag 07D9 (`lemma-derived-products`), and `homology.tex` Tag 0118 (`section-truncations`, the cochain formulas). The statement preserves all three blueprint assertions. The scheme is arbitrary; the finite extension E and finite-subextension condensed Qbar conventions agree with the chapter and coefficient definitions. No completeness, Noetherianity, common cohomological bound, or finite-family assumption enters.

- Step 1: checked `sk-def-sfb-module-objects`, `sk-def-sfb-sheaf-tensor`, and the complete statement of `lem-weil-pbc-ring-sheaves-grothendieck` against 03DB; PASS. The sheaf tensor universal property identifies internal actions with sectionwise module actions, so the general ring-sheaf theorem applies; exact filtered colimits of finite biproduct sequences prove exact sums. The general theorem is also already attached to closed slopmaster2 `SheafOfModules.isGrothendieckAbelian`, rather than assuming a constant scalar ring.
- Step 2: checked clause (1) of `det-def-localizing-closure-existence` against 07D9 (1)-(2); PASS. It states termwise coproducts for precisely these module objects. The two short exact sequences compute kernels, images, and cohomology after summing, with the canonical coprojections; the step uses the statement, not an implicit localization argument from its proof.
- Step 3: checked the final direct-sum sentence of `det-ind-heart-filtered-colimits` against its current blueprint statement and the inline Dic predicate; PASS. Its coefficient choices are exactly E and Qbar and it supplies arbitrary sums, so the cohomology comparison proves Dic closure.
- Step 4: checked `lem-weil-pbc-truncation-cohomology` and both canonical cochain constructions in 0118, together with clauses (1)-(2) of `sk-def-sfb-constructible`; PASS after expanding the zero-model explanation and its quote. The quotient in degree n gives the written cycles and next boundaries. These kernel/cokernel constructions are functorial, so the formulas apply to quasi-isomorphisms and descend to the derived category.
- Step 5: checked the defining cohomology clause of `sk-def-sfb-bounded-constructible` and clauses (1)-(2) of `sk-def-sfb-constructible`; PASS after expanding the latter quote. A singleton filtered diagram proves the inclusion, with no use of the separate Noetherian triangulated assertion.
- Step 6: checked the full statement of `det-ambient-ind-derived-triangulated` and clause (2) of `det-def-localizing-closure-existence`; PASS. The preceding sum closure and containment satisfy every intersection/minimality hypothesis. Only the inclusion of Loc(Dbc) is asserted; truncation stability of Loc(Dbc) is not used.
- New nodes: none; B1-B7 and new-node elimination are vacuous. Searches for 03DB, 07D9, 0118 and IndCons/Dic across the DAG and the current blueprint confirm reuse of existing tools, rather than adding elementary, duplicate, or restatement nodes.

Small cases checked: empty and singleton families; zero sheaves and complexes; the empty scheme and a field base; a family of shifts with no common bound; n=0 and n=1; a complex concentrated at the cutoff and one with a nonzero differential crossing it. Empty sums give zero, the one-stratum zero local model is valid on every affine, and both truncations give exactly the claimed surviving cohomology degrees. The dependency traversal has no path back to this item. All eleven citation quotes were checked as literal substrings, and proof_deps equals the union of step uses.

Independent Mathlib searches through msearch.py used LeanFinder `DerivedCategory homology functor preserves coproducts exact direct sums Grothendieck category`, Loogle `"homologyFunctor", "PreservesColimits"`, and grep `\bIndCons\b|ind.?constructible|indConstructible` in CategoryTheory. The semantic hits give generic homology functors, their factorization, homologicality, or unrelated preservation statements; the latter two searches give no hits. I read `DerivedCategory/HomologySequence.lean`, notably homologyFunctor, homologyFunctorFactors and the homological instance: none states this item. The broader case-insensitive grep also matched `findConstVal` names; these are irrelevant string matches, not ind-constructibility declarations. Direct read-only searches of slopmaster2 by the item id and ind-constructible terminology found no attachment. Actual search records remain in searches.jsonl and the relevant independent queries are appended to the item.

Changes made:

- Expanded both constructibility citation quotes to include its stratification and affine-local clause, so the quotations support the zero-sheaf assertion they justify.
- Wrote the one-stratum, scalar-module-zero argument in step 4, covering arbitrary schemes explicitly.
- Added the independently run Mathlib queries and this step-by-step second reading. All original worker sections, including `## Review by Q29`, remain in place. No new node or Mathlib leaf was needed; the three assertions and proof route are unchanged.

Second-reader validation: the first dry run reached preflight but the shared origin/newtargets-dag reference advanced while it ran. Preflight consequently reported HEAD not on top of that reference and three unrelated coordination-file differences (blueprint-index.tsv, queue.md, queue.tsv). None is present in this sandbox delivery. Retrying the unchanged mathematical repair through deliver.py rebuilds it on the current base; no direct git command or shared-repository edit is used.
