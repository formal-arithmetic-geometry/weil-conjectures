# NX stage-1 delivery: lem-sf-supported-tor-reduction-propagation

## Files written

- dag/nodes/sec-smooth-purity/lem-sf-supported-tor-reduction-propagation.json: existing statement, now split into six proof steps. Mathlib verdict: no match for the whole statement. Its statement, statement dependencies and imported metadata are retained.
- citations.json: one verbatim quotation from the statement of every node cited by every proof step.
- searches.jsonl: actual msearch.py log for this item; prior searches already present in the live node are retained there and the newly executed searches are appended to the node.
- report.md: this report.

There are **0 new nodes and 0 new Mathlib leaves**. All needed lemmas already exist. No Lean source, repository file, unit record or launcher file was written.

## Attachments

None. Read-only searches in lean/WeilConjectures for the exact blueprint tag and for supported/localization Tor and reduction terminology found no declaration giving the entire conditional quantitative statement, its integral uniformity and the restriction of the adjunctions. The upstream finite-coefficient Tor preservation declarations do not supply all these clauses. They are not an attachment for this item.

## WANTED

None. The current blueprint proof and the Stacks ringed-site and triangulated-category sources used below are available locally.

## Corrections and scope

No statement dispute and no change to the statement. The imported item was unsplit with no proof steps. Its hypotheses already provide finite interval preservation, constructibility, supported distinguished triangles, the closed pullback-pushforward isomorphism, and the canonical integral reductions preserving adjunction data. These are used as hypotheses, rather than reproved from geometric cohomological-dimension or projection-formula claims.

The source's residue calculation can be proved directly for every module sheaf by the existing Tor-interval triangle lemma. Thus there is no new residue criterion or geometric projection formula to establish. Inverse rotation gives C[-1] -> F -> K; this is essential to the sign of the upper-bound shift. The shift is +1 for C[-1], hence the bound is b+N+1.

I deliberately did not cite lem-weil-integral-ctf-triangulated: its statement fixes the global finite-field datum, whereas this item allows an arbitrary field k. Step 5 proves the needed integral closure from the general ambient integral triangulation, exact reduction, finite shift formula and triangle interval lemma. This retains all hypotheses of the present statement without importing a finite-field restriction.

## Not duplicates

No new nodes. The search found and reused lem-weil-proetale-tor-interval-triangle, lem-weil-finite-ctf-triangulated, lem-weil-integral-constructible-triangulated and lem-pur-derived-change-of-rings. Searches of the whole DAG and blueprint for Tor intervals and Tor amplitude revealed no separate blueprint node stating this entire conditional propagation-and-restriction assertion. The parent prop-sf-localization-all-stages contains this argument as part of its larger theorem; citing it would be circular. The item's same_as remains empty.

## Mathlib searches

All current Mathlib searches were executed with the required msearch.py command and their hits were read. Two semantic phrasings returned ordinary derived-category t-structure bounds, bounded representatives, fractions, or a homological-functor localization theorem. Loogle returned triangulated localization/exact/derived functors, and LeanSearch returned scheme immersion declarations. The targeted grep returned no supported Tor/reduction declaration. These component results do not state the whole item and are not one-line specializations proving it. No new Mathlib leaf is claimed. The item's older search records are preserved, including its explicitly unavailable old LeanSearch request.

## Review by NX

I read the entire current blueprint prop-sf-localization-all-stages.proof.md, particularly Finite Tor amplitude, (2') at the finite stage and Other stages, together with the chapter and unit route. I read Stacks sites-cohomology.tex, lemma-cone-tor-amplitude (Tag 08G2), including its rotation/long-exact-sequence argument, definition-tor-amplitude, and lemma-derived-base-change (Tag 06YY), and derived.tex, definition-triangulated-subcategory (Tag 05QM) and lemma-triangulated-subcategory. The blueprint supplies the assembly route; the proof is marked agent-origin because that blueprint is agent-written. There is no new node requiring a separate source review, and no prohibited SGA source is used.

For step 1, I opened def-weil-finite-tor-amplitude and lem-weil-finite-ctf-triangulated. The first defines finite Tor by an all-module interval and the second explicitly gives the integer shift formula. K and C are bounded constructible by the item's preservation assumptions. The shift formula is applied to C with m=-1, giving [a+1,b+N+1], and never assumes F already has finite Tor.

For step 2, I opened def-weil-triangulated-category and lem-weil-proetale-tor-interval-triangle. The former states the rotation axiom; the latter states a bound for the middle vertex of a distinguished triangle with arbitrary outside intervals on the small pro-etale site and for an arbitrary commutative coefficient ring. This is precisely C[-1] -> F -> K, with coefficients A_n and all-module Tor, so its hypotheses match. N>=0 makes the interval hull exactly [a,b+N+1]. No theorem about residue detection, exactness of closed pushforward, or tensor-pullback comparison is smuggled into this step.

For step 3, i^* interval preservation and i^*i_*=1 are explicit hypotheses. I checked the definition node really quantifies over every module sheaf; the constant residue sheaf is one such degree-zero module on each of X and Z. The two residue conclusions therefore follow without constructibility of a residue tensor or any unproved projection formula.

For step 4, the same definition node explicitly defines the integral condition using one interval for all derived reductions. Each comparison (TK)_n = T_nK_n is assumed in the item. I checked all five operation bounds separately and used no claim that an inverse limit preserves a cohomological interval. N is fixed across n; integral constructibility is assumed separately and is not inferred from Tor bounds.

For step 5, I opened lem-weil-integral-constructible-triangulated, lem-pur-derived-change-of-rings, def-weil-integral-derived-reduction, and def-weil-triangulated-subcategory as well as the two finite interval nodes. The ambient triangulation lemma is for a scheme, not specifically a finite-field base. Derived change of rings is exact for a sheaf-ring map on any site; the reduction definition identifies precisely the completed coefficient sheaf quotient functor in this application. Hence reduction sends each integral distinguished triangle to a finite one. Zero, isomorphisms, shifts and extensions retain bounds uniform in n; the displayed minimum/maximum bound is independent of n. These statements supply every closure condition of the full triangulated-subcategory definition. Any ambient characteristic notation is just the requirement ell invertible in the present k; no finite-field structure is used.

For step 6, I checked the subcategory node states exactly that distinguished triangles are inherited when all vertices belong. Fullness gives identical Hom sets, so the ambient adjunction bijections and their naturality restrict with the same maps and identities. The inverse of the assumed unit is an arrow of the full subcategory. The vanishing assumption is used only conditionally, as in the item's statement. The coefficient definition explicitly makes both field-stage categories equal; no rationalization or filtered-colimit comparison is newly asserted.

I checked n=1, N=0, a=b, K=0, the empty closed or open part, and i=id (with empty complementary open). For N=0 the allowed upper endpoint remains b+1, as the inverse rotation requires; the identity-immersion case satisfies this possibly loose bound. Non-flat residue modules over A_n for n>1 are legitimate tests, and the proof never treats the residue field as A_n-flat. There is no division by a uniformizer and no assumption that bounded constructible implies finite Tor. Every proof step is shorter than 2000 characters; the elementary steps use only the cited explicit formulae, the item's assumptions and fullness. The non-elementary interval and triangle-closure assertions are cited. citations.json contains only verbatim substrings of the opened statements. The off-unit generic tools are declared in split_report.tool_uses with their purposes; the localization route is unchanged.

## Unfinished work

None in this one-level split. Existing cited statements remain their own items. The server review_split check passed. The required deliver.py --no-push completed with exit 0 and preflight passed (ecde6ebf5a9); the final report is rechecked by the subsequent dry run and push.
