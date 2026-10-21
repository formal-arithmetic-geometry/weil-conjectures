# Worker report

Item: lem-sfb-amplitude-truncation-family-comparison. Group Q04, 2026-10-21.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-amplitude-truncation-family-comparison.json: statement unchanged; nine proof steps; status split; no Mathlib match.
- citations.json: one verbatim statement excerpt for each of the 17 step/node citations.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. Nothing in the shared repository or launcher was written, and no compiler, Lake or build was run.

## Attachments

None for this item. I searched WeilConjectures for the exact blueprint tag and for amplitude, truncation, family, coproduct and finite-window terminology. CoproductsOfFiniteAmplitude.lean:121 has DerivedCategory.isIso_sigmaComparison_of_bounded, with its four intermediate maps proved locally inside its proof. Its exported statement assumes a triangulated class of complexes, closure under sums and truncation, and preservation of bounded-family sums; those are not hypotheses of this item. Its conclusion is the coproduct comparison, rather than the four truncation maps. It is therefore not an attachment. PlusDevissage.lean:134 gives only the upper arrow in bounded-below derived categories. HomologyCoproducts.lean:48 gives a tool already accessible through the existing exact-colimit homology and derived-coproduct nodes, not the item itself.

## WANTED

None. All sources used were available locally.

## Audit and changes

The seeded item was statement-only. Its statement is true with the exact hypotheses given, so no statement correction or STATEMENT-DISPUTED is needed. In particular, the class P need not be Serre, extension closed, or closed under summands. A direct application of the exported finite-amplitude coproduct theorem would impose extra hypotheses. Instead the split uses the canonical truncation triangles themselves and writes the elementary assembly of all four maps.

I read the chapter sec-six-functors-basics, unit sk-prop-ctf-finite-proper, and its current main-20261015 localizing proof. The split realizes the finite-window argument extracted from that proof, serving its direct-sum assertion. It introduces no different geometric or coefficient route and does not change a unit or chapter record. Blueprint searches for truncation, amplitude and finite window found no same statement: det-finite-window-reduction concerns Hom from a fixed constructible object, not cohomology after G. The existing parent continues to use this item's unchanged four-map assertion.

## Mathlib searches

The four historical searches in the imported node were retained. Four additional actual searches were run with msearch.py and appended exactly from searches.jsonl: LeanFinder for the finite-amplitude four-map family assertion, Loogle `DerivedCategory.homologyFunctor, "trunc"`, grep `isIso.*[Tt]runc|[Tt]runc.*[Ii]sIso|[Aa]mplitude` in Algebra/Homology/DerivedCategory, and LeanSearch with a second finite-window phrasing. All services answered. The hits provide individual truncation maps, quasi-isomorphism criteria, cone-triangle transport, and definitions of triangulated functors; none states the item. I read Fractions.lean:65-110: the hits there represent a derived morphism by a fraction with a bounded representative, not finite-amplitude or family isomorphisms. I also read the displayed definitions of truncation maps and the exact source theorem above. No fabricated or unavailable-as-no-match search was recorded.

## Not duplicates

No new nodes or duplicate pairs. Existing general results were reused: lem-kun-grothendieck-derived-coproducts rather than a new coproduct node; src-weil-homology-preserves-exact-colimits rather than a new cohomology/sum node; lem-sfb-arrow-exact-colimits rather than a new kernel/cokernel lemma; and the existing Mathlib leaves for truncation triangles and long exact cohomology.

## Review by Q04

I checked delivery-errors B through E with the node files and sources open. The item is an abstract lemma, not a theorem quoted wholesale from Stacks. Its source is the main-20261015 localizing proof's finite-window paragraph. I read injectives.tex Tag 079B (definition-grothendieck-conditions, and the discussion of AB4/AB5), Tag 07D9 (lemma-derived-products, both coproduct clauses and the Hom computation), and derived.tex Tag 08J5 (remark-truncation-distinguished-triangle). I also read the homological functor discussion at Tag 0147 and the cohomology lemma Tag 05RS. The proof is marked agent because the assembly of these results is supplied here.

Step 1 uses exactly the filtered finite-limit preservation asserted by lem-sfb-grothendieck-filtered-finite-limits. I spelled out why the coproduct functor is the filtered colimit of its finite subcoproduct functors and why finite subcoproducts preserve finite limits. This is the elementary AB5-to-AB4 argument, retained as a step rather than a new node. The finite-subset indexing poset is small in the fixed indexing universe, including for the empty set; no larger index category is introduced.

Step 2 uses the statement of lem-kun-grothendieck-derived-coproducts, including its specified termwise coprojections. It does not take a cohomology-preservation assertion from that node's proof. The separate statement src-weil-homology-preserves-exact-colimits supplies precisely homology preservation for a discrete indexing category, with no filteredness requirement. I read that node and DegreewiseLimits.lean:76-89 and :142-144. Step 1 verifies its exactness hypothesis for both A and B; def-weil-abstract-derived-category explicitly supplies factorization of cohomology through localization. Naturality of theta is checked on the coprojections. Closure of P under sums and isomorphisms is sufficient here.

Step 3 reads the actual kernel/cokernel truncation formulas and retained-cohomology sentence in def-kun-truncations, and the cohomological meaning of both bounds in def-sbc-standard-tstructure-derived-category. The new cohomology objects are either old ones or zero. Thus no unstated subquotient or extension closure of P enters. The common window is [m-c,m], including when c=0.

Step 4 cites the actual statement of lem-sfb-arrow-exact-colimits, not its construction. Step 1 verifies existence of the discrete colimits and preservation of finite limits, exactly that node's hypotheses. Its conclusion preserves the canonical kernel inclusions and cokernel projections; the good-truncation formulas then identify alpha and beta degree by degree. I wrote both equations relating alpha/beta to the specified u/v maps. The identification concerns the ambient coproducts from step 2, with their specified coprojections, rather than an abstract isomorphism between unrelated objects.

Steps 5 and 6 each cite lem-sf-derived-truncation-triangle and lem-sf-derived-homology-long-exact, whose statements I opened. The first applies with threshold m+1; its third object is in degrees at least m+1. The second applies with threshold a=m-c; its first object is tau at most a-1. Exactness of G is precisely the additive distinguished-triangle preservation defined by def-weil-triangulated-category. After applying G the first argument kills degrees m-1 and m in the third object. The second kills degrees m and m+1 in the first object, since (a-1)+c=m-1. Both long exact segments are displayed, so there is no hidden connecting-map argument or off-by-one assumption. The upper-amplitude hypothesis is used only on a truncation with P-cohomology. The sum of U_s has P-cohomology by steps 2-3, so that same application is justified for the ambient sum.

Step 7 combines the earlier two triangle arguments with the two explicit canonical-map equations; it only uses composition and cancellation of isomorphisms. Step 8 uses the natural cohomology/coproduct isomorphism already established in step 2 in B, not any claim that G commutes with coproducts. The inverse to the coproduct of invertible maps is written as the coproduct of their inverses. Step 9 checks the actual natural arrows and gives the zero-object argument for the empty family. Thus all four maps, naturality, and absence of a common bound are covered. Every step is under 1000 characters, so none crosses the long-step threshold or hides a separately named standard comparison.

I tested I empty, a singleton, c=0, zero complexes, G the identity (c=0), and G=id plus the shift [-c] on D(Ab). The last example puts nonzero cohomology at the top allowed degree b+c and verifies the lower cutoff m-c, including its endpoint. Unbounded families such as K_s=Z[-s] are allowed: the proof applies the same m,c without imposing a family bound. The triangle estimates and both canonical arrow directions remain correct in each case.

The three off-unit citations declared in split_report.tool_uses are generic categorical tools (ambient coproducts, exact-colimit homology, and arrow kernels/cokernels). They do not replace the unit's proper-base-change or coefficient-comparison route. All other proof citations are definitions or Mathlib leaves. No unproved project declaration is offered as a finished proof of the item, no new node restates a clause, and no source from the prohibited SGA route is used.

## Unfinished work

None in the requested one-level split. Existing dependencies retain their own project status. Delivery validation is run by deliver.py on the Weil server; its outcome is reported by the delivery command.
