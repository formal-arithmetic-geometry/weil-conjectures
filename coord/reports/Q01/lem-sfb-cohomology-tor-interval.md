# Stage-1 delivery: lem-sfb-cohomology-tor-interval

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-cohomology-tor-interval.json`: statement; split into five proof steps using existing nodes. The statement and its original statement dependencies are unchanged. Mathlib verdict: no match.
- `citations.json`: one entry for each step/node citation, with a contiguous verbatim excerpt of the statement actually used.
- `report.md`: this report. The search command also wrote `searches.jsonl`.

No new nodes; no new Mathlib leaves; no Lean files or compiler calls.

## Attachments

None. I searched `lean/WeilConjectures/` by the exact blueprint id and searched the Tor-amplitude infrastructure by cohomology, homology, and Tor-amplitude names. There is no declaration tagged with this item. `DerivedCategory.isZero_homologyFunctor_tensor_of_torAmplitudeIn` in `CategoryTheory/DerivedCategory/TorAmplitudeHomology.lean` assumes one tensor factor has amplitude [0,0]; it does not give the item's hypothesis on each cohomology module. `homologyConcentratedIn_tensor_of_torAmplitudeIn_left` in `CategoryTheory/DerivedCategory/FlatModel.lean` assumes Tor amplitude of the entire factor, not of its cohomology objects. The termwise bounded-projective restriction result is also not a cohomology-module bound. None is an exact attachment.

## Literature wanted

WANTED: none. All sources used are present in the read clone.

## Corrections and route

The item had an empty proof. I supplied the proof without changing its statement. The main-20261015 source's Complexes paragraph proves the specialization [c,d]=[-1,0]. The item's generalization uses precisely the same successive-truncation and extension route. The chapter and localizing-closure unit records were read; neither was modified. There is no replacement of the unit route and no statement dispute.

A potential sign mistake was checked explicitly: a cohomology module in degree q is M[-q], so its tensor cohomology in degree r is H^(r-q)(M tensor^L N). Its interval is [q+c,q+d], as required. Merely quoting the positive-shift clause of the Tor-amplitude definition would not justify arbitrary negative q; step 2 instead cites exactness of relative derived tensor and the definition of an exact functor to handle all integer shifts. Interval enlargement is written as the two inequalities, not made into a new node.

## Unfinished work

No mathematical part of this one-level stage-1 split remains unfinished. The existing dependencies keep their current states and are not split or modified by this delivery. Validation and delivery use the required server-side tool.

## Not duplicates

No new nodes are created. Existing statements for truncation descent, successive-truncation triangles, relative tensor exactness, and amplitude stability are reused. Whole-DAG searches by Tor amplitude, cohomology Tor interval, Postnikov, shifts, and truncation triangle were read. `tools/blueprint_refs.py ancestor lem-sfb-cohomology-tor-interval` identifies `det-def-localizing-closure-ctf-equals-bc`; whole-blueprint searches for `Tor amplitude`, `cohomology Tor`, `truncation`, `truncation-triangle`, and `ringed-projection-mate-exact` produced no second blueprint node with the item's statement. Its existing precise `blueprint.from.place` and `via` are retained, and `same_as` is [].

## Mathlib searches

I retained the item's earlier Q32 search records. I also ran the required logged `msearch.py` commands for this item with LeanFinder, Loogle, grep and LeanSearch, plus a second LeanFinder phrasing. All five services/calls succeeded; none is reported unavailable. The exact query strings and returned hit names are appended to `mathlib_searches` and present in `searches.jsonl`.

The first LeanFinder query returns canonical t-structure bounds and a shift lemma, which do not assert the universal tensor test. The second returns vanishing of positive Tor for projective objects, K-projective complexes and projective-dimension criteria. Those do not apply to arbitrary cohomology modules of a sheaf complex under the item's assumptions. LeanSearch returns projective/injective dimension, module-sheaf limits, and a bounded representative theorem; that representative need not have flat terms and so cannot itself give the asserted Tor bound. Loogle and the Mathlib grep for Tor-amplitude names return zero hits. Generic infrastructure is therefore reused as proof material, not recorded as an exact Mathlib leaf.

## Review by Q01

I read the item's source `sk-def-localizing-closure-ctf-equals-bc.proof.md`, in the current main-20261015 snapshot, including its Complexes paragraph and its preceding module-level bounds. I read the companion Tor-amplitude definition and proof, particularly its shift, extension and isomorphism clauses. I read Stacks `derived.tex`, Tag 08J5 (`remark-truncation-distinguished-triangle`), which explicitly gives successive good truncations with quotient H^q[-q]; `homology.tex`, Tag 0118 (`section-truncations`), with the retained and vanishing cohomology of good truncations; and `sites-cohomology.tex`, Tag 06YU (`definition-derived-tor`), which defines the relative derived tensor as an exact functor after a K-flat replacement. The preceding K-flat resolution and exact-functor construction were also read. These are ordinary ringed-site statements; no SGA route is used. There are no new node sources to audit.

For step 1 I opened the statements of `def-weil-sheaf-of-modules-category`, `def-weil-abstract-derived-category` and `lem-weil-pbc-truncation-descends`. The first says the sectionwise module category is abelian under the small-site universe convention; the second defines localization at quasi-isomorphisms; the third explicitly states H^r(tau_<=q K)=H^r(K) for r<=q and zero otherwise. The proof uses that actual formula to check both endpoint maps in every degree. It does not infer acyclicity from a bound in only one direction. The small-site convention is available for the small pro-etale site, with the ordinary universe enlargement used in the cited definition.

For step 2 I opened `lem-weil-pbc-ringed-projection-mate-exact` and used only its sentence that derived tensor is exact in each variable. Its ringed-site hypotheses hold for the identity of the small pro-etale topos with the commutative sheaf Lambda_X; it imposes no finite-type, noetherian, constructibility or discrete-ring hypothesis. `def-weil-triangulated-category` explicitly defines an exact functor to include the shift comparison. Iterating that comparison and its inverse gives arbitrary integer shifts. The cohomology reindexing is written from the actual complex-shift formula in `def-weil-abstract-derived-category`; the tensor test is exactly clause 3 of `det-def-sfb-constructible-tor-amplitude`. Thus no coefficient-category change or uncited projection formula is being used.

For step 3 I checked [q+c,q+d] is contained in [a+c,b+d] using q>=a and q<=b, with no assumption about the signs of a,b,c,d. Widening an interval is a direct implication between its vanishing conditions. Exact tensor is additive, so zero tensors to zero. The cited amplitude node explicitly states isomorphism invariance, which carries this fact to the lower endpoint. These are short elementary consequences of the cited statements; they are steps, not new nodes.

For step 4 I opened the whole statement of `lem-weil-pbc-truncation-triangle`. It quantifies over any abelian category, and supplies the distinguished triangle whose middle object is the successive good truncation and whose third object is H^q(K)[-q]. Its extra functoriality and bounded-below application are unused; there is no etale-site restriction in its initial assertion. The amplitude node's statement expressly gives the middle-object extension rule when both outer objects have the SAME interval. The induction is on m=0,...,b-a+1, with q=a+m in each step and lower endpoint a-1. In particular it is finite even though a and b are arbitrary integers, and it never assumes a truncation is already of finite Tor amplitude in order to establish that fact.

For step 5 I checked that the upper endpoint map was already proved to be a quasi-isomorphism in step 1; the amplitude node's actual isomorphism-invariance clause applies. No theorem about constructibility is used. Generic dependencies from other units are declared in `split_report.tool_uses` with their precise purposes. They support the blueprint's truncation route as black boxes.

I checked delivery-errors B--E against the files: there are no statement-only child nodes with hidden proofs, no new definitions or duplicate notions, no unrecorded Mathlib queries, and no relocation of the item's conclusion into a new lemma. Every non-elementary input is a cited existing statement and `citations.json` quotes it verbatim. The proof uses no small-index colimit or hypercohomology spectral sequence and therefore needs no convergence or completeness theorem. Each proof step is under 2000 characters; no comparison argument or hidden standalone lemma is bundled into a long step.

Edge cases: for K=0 and for the empty scheme all tensors vanish, giving any ordered interval. For a=b the induction has exactly one triangle with zero first object and gives the single shifted-module interval [a+c,a+d]. A flat module in degree q with [c,d]=[0,0] gives [q,q], confirming the shift sign also for q negative. For a=2,b=3,c=-1,d=0 the two outer shifted intervals [1,2] and [2,3] fit in [1,3]. For an all-negative window, a=-3,b=-2 and the same Tor interval give [-4,-2]. Allowing c<d or wider-than-necessary cohomology bounds only widens the conclusion. A zero coefficient ring also causes no failure. Nothing assumes cohomology modules of a finite-Tor complex themselves have finite Tor amplitude: that false converse is not used.
