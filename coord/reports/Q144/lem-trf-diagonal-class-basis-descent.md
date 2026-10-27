# Worker report — Q144

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-diagonal-class-basis-descent.json`: statement, split into six proof steps; no Mathlib match. The statement and statement dependencies are unchanged.
- `citations.json`: eight verbatim statement excerpts, one for each step/node citation.
- `searches.jsonl`: actual results of five Mathlib searches, retained without alteration.

There are **0 new nodes and 0 new Mathlib leaves**. All non-elementary inputs already have nodes. The sandbox also contains the preparation script used to write the JSON; it is not a delivery file.

## Attachments

None. Searched the live `lean/WeilConjectures/` by the exact blueprint tag and by diagonal-class, normalized-isomorphism and basis-descent terminology. No project declaration states this result. The etale smooth-purity diagonal class is a different coefficient category and statement.

## WANTED

None. The necessary Stacks sources are present.

## Findings and changes

The supplied item had a statement but no proof. Its gluing input is already `lem-trf-derived-basis-local-hom-glue`, a more general Hom-bijection theorem for intersection-refining open families with negative cross Ext vanishing. The generic BBD object-descent theorem is not needed anew: the global objects K and L are already supplied. I used the Hom theorem to glue the map and its inverse, with uniqueness proved by its injectivity clause.

The important global-equality issue is that the opens U ×_S U need not cover Y = X ×_S X. The proof therefore constructs the scalar identification first and establishes its restriction formula before detecting equality by the structure sheaf on X. For example, for a discrete two-point X over a field and the singleton basis, the two double opens omit both off-diagonal points. This example invalidates a double-open cover argument, but causes no problem for the proof delivered here.

The item's reference to `def-trf-coherent-relative-dualizing-pair` is used only for the formula defining multiplication and its transpose. I never assume K or L is a relative dualizing pair, nor use that definition's flatness, finite-presentation, pseudo-coherence or Tor-amplitude predicates. Those hypotheses are unnecessary because the needed multiplication isomorphism and local normalized isomorphisms are explicit hypotheses of this item. The elementary direct-image restriction identification is computed on sections in Step 4; the derived pullback restriction identifications are stipulated in the item.

Mathlib searches used leanfinder twice with different phrasings, leansearch, loogle, and source grep. I read the returned types: ordinary sheaf gluing requires an actual sheaf of local Hom already, and `DerivedCategory.isIso_iff` is an isomorphism test rather than a derived Hom gluing theorem. I also read `Mathlib/Topology/Sheaves/SheafCondition/UniqueGluing.lean:180,188` and `Mathlib/Algebra/Homology/DerivedCategory/HomologySequence.lean:88`. None states the item or a one-line specialization of it. Earlier searches in the item have been retained, and the new queries/results are copied from this run's log.

Blueprint searches for “diagonal class”, “normalized diagonal”, “negative self”, “relative dualizing”, and “derived internal Hom sections” found no equivalent blueprint node. The current `main-20261015` proof of `lem-trf-local-term-locality` and the unit/chapter records were read. This item is the explicitly recorded supporting gluing component down the inherited relative-dualizing-pair chain, not an alteration to that chapter or unit's proof route. `blueprint.from.place` was already precise and is retained. Its `same_as` is the searched empty list.

## Not duplicates

No new nodes are proposed. The pre-existing gluing, global Hom, degree-zero sections and restriction-transposition nodes are cited directly.

## Review by Q144

I read `duality.tex` Tag 0E2W (`lemma-uniqueness-relative-dualizing`) in full, including its final gluing paragraph and the adjacent existence proof that invokes BBD. I read `cohomology.tex` Tag 0D66 (`lemma-vanishing-and-glueing`), Tag 0D68 (`lemma-uniqueness`), and the full statement/proof of Tag 0D6C (`theorem-glueing-bbd-general`). For the scalar and restriction arguments I read `sites-cohomology.tex` Tag 08JA (`lemma-section-RHom-over-U`) and Tag 08JB (`lemma-restriction-RHom-to-U`), plus the tensor-Hom construction in Tag 08J9. I checked the zeroth right-derived comparison against `derived.tex` Tag 05TD (`lemma-left-exact-higher-derived`) and the nonnegative injective-resolution construction in Tag 013K. There are no new nodes requiring separate sources.

Step 1 uses only the assumed canonical identifications, functoriality of restriction and local uniqueness. In particular, uniqueness is invoked on V, which is itself a basis member; it is not asserted without proof on an arbitrary intersection. Intersections are covered by smaller basis opens, which verifies the precise hypothesis of the gluing theorem used next.

For Step 2 I opened `lem-trf-derived-basis-local-hom-glue` and checked that its statement gives a bijection for inclusion-compatible families, not merely a sheaf under stronger intersection assumptions. Its negative-Hom hypothesis is verified for all four pairs by composing with the supplied local isomorphism and its shifts. This justifies gluing both directions and detecting both inverse equations; it also proves uniqueness among all maps with the local restrictions. No object-existence assertion or finite-cover reduction is hidden here.

For Step 3 I opened `lem-pur-rhom-global-sections`, whose statement identifies the global derived Hom with zeroth hypercohomology, and `lem-sc-open-cohomology-zero-sections`, whose statement identifies zeroth derived sections of a module with ordinary sections. The Zariski sites of Y and of every Y_U are small: their objects are the set of opens, and each Hom is empty or a singleton. Their structure sheaves are commutative. The latter comparison is applied only to the module Δ_*O_X in degree zero, not to an arbitrary unbounded object. The only unbounded object involved in the other comparison is allowed by the former node. I read `def-trf-coherent-relative-dualizing-pair` to check its actual transpose formula, and evaluated that formula at s: it is η composed with multiplication by s. Evaluation at the unit gives η, and the multiplication equations give linearity for the natural diagonal-module action. This explains both normalization and the particular canonical identification, rather than merely asserting existence of an abstract group isomorphism.

For Step 4 I opened `lem-weil-pbc-ringed-internal-hom-exact-restriction`: its statement supplies an actual natural isomorphism for arbitrary unbounded objects, with successive-restriction compatibility. I separately opened `lem-weil-pbc-ringed-slice-evaluation-transpose`: its displayed transposition equation supplies exactly the compatibility for the specific multiplication map. The site localization is an open restriction with identity coefficient-ring map, so the theorem's hypotheses hold. Both are generic tools recorded in `split_report.tool_uses`; they do not introduce an alternative route. I checked that the other two citations provide the same global Hom and degree-zero comparisons on Y_U. The inverse formula from Step 3 makes the restriction square explicit: restriction of η composed with m_s is η_U composed with m_(s|U). No claim about arbitrary point inverse image commuting with internal Hom is used.

Steps 5 and 6 are elementary deductions from those established facts. Step 5 calculates the restrictions of the scalar s, then uses separatedness of the actual structure sheaf on the basis cover of X to conclude s = 1. Step 6 restricts a competing normalized isomorphism, applies the assumed local uniqueness, and invokes the already proved global Hom injectivity. The existence, local-restriction uniqueness, scalar identification, normalization compatibility, global class equality and final uniqueness clauses are all accounted for.

I checked the B–E return checklist against these files. The proof never cites a node's proof for an unstated conclusion; all eight quotes in `citations.json` are literal substrings of the statements read. There is no added statement, duplicate, hidden unsplit elementary lemma, Mathlib leaf claim, cycle through the item's parent rigidity theorem, or SGA citation. The largest proof step has 1255 characters, so none meets the 2000-character long-step review threshold.

The small cases checked were the empty scheme with empty or nonempty empty-open basis, a point, the zero local complex, a basis not closed under intersections, an infinite/non-quasi-compact basis, and the disconnected two-point example where the double opens do not cover the product. On the empty scheme all Hom sets and section sets are singletons and the zero ring has 1 = 0. When a local K is zero, its specified isomorphism forces local L to be zero, so all four negative-Hom checks and inverse equations still hold. No finite cover, affine intersection or noetherian hypothesis has entered the proof.

## Unfinished work

None in the authorized stage-1 scope. No Lean was written and no compiler, Lake or build tool was run.

## Returned landing repair — 2026-10-23

The return entry at 04:18 UTC names returned head `a37c68732e9`: the reader approved the split, but L could not land a side completion that had not been promoted into the live DAG. I continued the delivered sandbox as instructed, preserving its six-step proof, citations, report and actual search log. The required initial dry run completed successfully at `950b19f8f3a`; deliver.py rebuilt the retained files on current `origin/sheaf-dag`. The current live item is still `unsplit`, with empty proof and no review. Its statement, statement dependencies, source, blueprint ancestry and created metadata agree with the retained version. There is no released repair note for this item.

I reread every current statement dependency and all six current proof dependencies, rather than assuming their returned-head versions still apply. For Step 2 the basis-Hom theorem still supplies precisely the compatible-family bijection and its injectivity for all four pairs; the given local isomorphisms verify the negative cross-Hom hypotheses. For Step 3 the global-Hom statement is valid on a small commutative ringed site; the degree-zero comparison concerns an ordinary module; the dualizing-pair definition supplies exactly the transposed multiplication formula. In Step 4 the current slice-transposition statement explicitly normalizes the tensor and internal-Hom comparisons and states the transposition equation for arbitrary unbounded objects. I wrote out the resulting equality between restricted multiplication and local multiplication using the comparison theta; thus its being an isomorphism follows from two identified isomorphisms. The eight citation quotes remain literal excerpts of the current statements. No dependency needs replacement.

I reopened Stacks `duality.tex`, Tag 0E2W (`lemma-uniqueness-relative-dualizing`), `cohomology.tex`, Tags 0D66 and 0D68, `sites-cohomology.tex`, Tags 08JA and 08JB and the tensor-Hom argument between them, and `derived.tex`, Tag 05TD (`lemma-left-exact-higher-derived`). Step 3's source now names 05TD(3), the actual zeroth-derived comparison, instead of the old general cohomology-section pointer. The maps and hypotheses in the split are unchanged. Steps 1, 5 and 6 remain the elementary compatibility, scalar separatedness and uniqueness arguments. The empty scheme, zero local complex, non-intersection-closed and infinite bases, and the two-point example with missing off-diagonal double opens still pass the checks in my signed review above. All proof steps remain under 2000 characters.

I reread `searches.jsonl` and the recorded hits, and reopened the ordinary sheaf gluing declarations and the derived-category isomorphism test. Their statements still do not supply this theorem; its statement and search questions have not changed, so no searches were repeated or invented. The fresh exact-tag and concept search in current `lean/WeilConjectures/` found only the different etale trace-diagonal datum, not an attachment. The chapter and unit records and current blueprint locality statement were reread; this repair preserves the existing route. No new node, Mathlib leaf, Lean file or compiler invocation is introduced. This section supplements my `Review by Q144` signature and documents an adjusted delivery, not an unchanged re-push.
