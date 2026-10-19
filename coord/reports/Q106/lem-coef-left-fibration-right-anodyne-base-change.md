## Files written

- `dag/nodes/sec-six-functors/lem-coef-left-fibration-right-anodyne-base-change.json`: item, statement unchanged, split in eight steps; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-right-anodyne-mono-cancellation.json`: one new statement-only node, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and targeted Mathlib grep.
- `citations.json`: verbatim statement excerpts for every citation in each item step.
- `searches.jsonl`: actual search-command log. The earlier searches already in the repository item were read and retained; this sandbox began without an item, report or search log.

## Attachments

None. Searched all of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id and for right-anodyne and left-fibration names and words. No relevant project declaration was found. The read-only upstream master search likewise has no such declaration; it is reference material only.

## Wanted sources

WANTED: Denis-Charles Cisinski, *Higher Categories and Homotopical Algebra*, `https://cisinski.app.uni-regensburg.de/CatLR.pdf`, Proposition 4.4.11 and Lemma 4.4.10 (printed pp.158–159), Lemma 3.1.3 (printed pp.74–76), and Corollary 4.1.10 (printed p.140), for lem-coef-left-fibration-right-anodyne-base-change and lem-coef-right-anodyne-mono-cancellation. The PDF was read online, without downloading or changing literature/. No archived copy was found by filename or in literature/LIST.md. The item's proof_origin is therefore agent, as required for an unarchived source. There is no Stacks tag for these simplicial one-sided-fibration assertions. No SGA source is used.

## Corrections and scope

The item had a complete correct statement but no proof. I retained its exact hypotheses, including arbitrary simplicial bases and total spaces, and its original source and blueprint ancestry. The unit is General Verdier biduality in Six Functors; this node is a technical descendant of the coefficient-adjunction foundation, not the unit's statement. No unit realization or route changes are appropriate.

The source compresses the relative homotopy lift into a reference to the proof of Proposition 2.5.7. Steps 3–5 supply that missing argument explicitly. Its reduction through Lemma 3.1.3 is expanded in Steps 6–7 instead of creating an endpoint-generation node. The cancellation fact genuinely needs an independent theorem: weak saturation alone does not assert it. It is the only new node; it neither restates the pullback theorem nor assumes its conclusion.

## Not duplicates

- lem-coef-right-anodyne-mono-cancellation vs lem-coef-infinity-right-anodyne-saturation: the existing statement is separate-variable saturation of pushout-products, not cancellation of composites.
- lem-coef-right-anodyne-mono-cancellation vs lem-coef-infinity-right-anodyne-product: the existing statement is the pushout-product theorem for a right-anodyne map and a monomorphism, not right cancellation.
- lem-coef-right-anodyne-mono-cancellation vs lem-coef-contravariant-slice-model: that statement says right-anodyne maps are trivial cofibrations but does not assert that all monic trivial cofibrations are right anodyne; therefore its statement alone does not give the cancellation conclusion.
- lem-coef-right-anodyne-mono-cancellation vs lem-coef-spine-cancellation-inner-horns: the existing statement assumes cancellation for an arbitrary class and deduces inner horns from spines; it does not prove right cancellation for the one-sided class.

Searches before creation: whole-DAG searches for right anodyne/left fibration, right-anodyne cancellation, the exact new id, and Corollary 4.1.10; whole-blueprint searches with blueprint_refs.py for `right anodyne`, `right-anodyne`, `anodyne`, and `cancellation`; project Lean searches by tag and concept. The three generic blueprint cancellation hits concern scheme-theoretic proper base change or finite surjections. They are unrelated. No existing node with the new statement was found.

## Review by Q106

I read the worker contract, delivery-errors B–E in full, the three blueprint levels in SETUP, GOAL, dag-sync, the chapter and unit records, the item, and the actual statements of every cited node. Online I read Cisinski Proposition 4.4.11 and Lemma 4.4.10, the explicit maps in the first half of Lemma 3.1.3, and the exact assertion of Corollary 4.1.10. The latter states precisely the new lemma: both maps are monomorphisms, the first is right anodyne, and the second is right anodyne exactly when their composite is. It assumes no fibrancy of its three objects.

Step 1 cites the actual degreewise-products/pullbacks convention, the horn-lifting definition of left fibrations, and the closure definition of right-anodyne maps. Pullback stability of left fibrations is proved by pairing a prescribed base simplex with its projected filler. Saturation is checked in each set of simplices: colimit identifications preserve the common base element. The retract argument pulls a given left fibration back along the codomain retraction before using membership of the larger arrow. This avoids silently requiring pullback stability of arbitrary right-anodyne maps.

Step 2 uses the new cancellation statement on E_A -> E_B -> E. Its first arrow is right anodyne because E_B -> B is a pullback of the given left fibration; its composite is right anodyne by the assumed membership of gf. All arrows to which cancellation is applied are monomorphisms. This is exactly the conclusion the new node states, and it is the non-elementary input isolated by this split.

Step 3 uses the existing right-anodyne pushout-product statement with the right horn {1} -> Delta^1 and the opposite of an arbitrary monomorphism. Its hypotheses permit arbitrary simplicial sets. I defined order reversal on the simplex operators, checked that it exchanges horn indices i and n-i, and used its degreewise preservation of the closure operations. Left horn lifting thus gives right horn lifting after reversal. Pushout and retract lifting are written directly; the cited Mathlib leaf lem-coef-transfinite-left-lifting supplies precisely the continuous small ordinal-chain case. Its category is sSet in the fixed containing universe, and the required colimits are degreewise colimits. It does not assume the class of right-side maps is small.

Step 4 uses the stated degreewise conventions and left-fibration lifting, applying Step 3 to K -> E. The maximum of two monotone [m] -> [1] maps is monotone and commutes with precomposition. The prescribed lift on {0} x E is the identity, on Delta^1 x K it is the inclusion independent of time, and the prescriptions agree on their intersection. At time 1 its base is in the terminal endpoint, so the lift factors through K. All three retraction and relative-homotopy identities are strict, not merely up to homotopy.

Step 5 uses the exact pushout-product conclusion with i:K -> E, which is monic. I wrote both arrow-category squares and verified that their composite is the identity. The direction of the homotopy is identity at time 0 and the retraction at time 1. The endpoint in this right-anodyne product is {1}, while the lifting in Step 3 used {0}; interchanging them would be a substantive error. The closure definition supplies passage to the arrow retract.

Step 6 has no new black box: the inclusion of {1} x B into the union is the pushout of e_A, and its composite with P(a) is e_B. Steps 1, 2 and 5 apply, with both maps monic. This elementary argument replaces a proposed new generating-criterion node.

Step 7 uses the cited node's explicit description of standard simplices as monotone maps and horns by missing a vertex other than k. I checked the maps s and r are monotone, that rs is identity, and that r takes the union into the horn. On the terminal endpoint it misses 0 (requiring k>0); on a simplex over the horn it cannot add any omitted vertex except k. These are the complete section/retraction-square checks, so there is no appeal to a missing unmarked prism-generation theorem. Step 8 uses only the minimal closure in the right-anodyne definition and the definition of C established in Step 1.

Small cases checked: an independent finite enumeration verified monotonicity of r, rs=id, and the horn-image condition on all 3,309 nondegenerate prism chains for 1 <= n <= 5 and every 0 < k <= n. In particular k=n and n=k=1 in the horn retract; the formulas remain valid and the final-endpoint part misses 0. Also checked the empty T endpoint case (all relevant arrows are empty identities), K=E (the relative lifting domain is the whole cylinder), and a left fibration with empty terminal fiber (the lifted endpoint forces the whole total space to be empty). The new cancellation statement is valid for identities and empty objects; for inclusions of subsets of a finite linear order, right-anodyneness is finality and is tested by containing the maximum. If A -> B contains max(B), then B -> C contains max(C) exactly when A -> C does, agreeing with the asserted cancellation. No new statement assumes nonemptiness or a dimension-zero horn.

For B1–B10 I checked the new file is a statement only, introduces all objects, names the definition it uses, has literal TeX once, gives the exact source place, records only searches that ran, and has complete blueprint.from/place/via and same_as. Mathlib searches returned ordinary cancellation and all-horn Kan facts. I read AnodyneExtensions/Basic.lean:63–93, CategoryWithFibrations.lean:35–106, and CategoryTheory/Category/Basic.lean:330–363; their statements do not specialize in one line to either the item or the new lemma. The DAG proof-dependency union is exact, and the new cancellation node depends only on definitions, so it cannot close a cycle through this item. All proof citations stay in the item's unit or are definitions or the existing Mathlib leaf. Nothing is left unfinished in the item's split; the independent cancellation statement is deliberately left unsplit for its own worker.

## Validation

Required server checks and full delivery dry run are run with the prescribed wrappers. The final accepted sandbox is left for the independent second reader; no push is authorized in this turn.


## Second reading by Q106

Independent reader, 2026-10-17. Read delivery-errors B–E, GOAL.md, dag-sync.md, the sandbox report and both node files, the current main-20261015 coefficient-adjunction proof, and every cited node statement. Read Cisinski online at https://cisinski.app.uni-regensburg.de/CatLR.pdf: Corollary 4.1.10 (printed p.140), Lemma 3.1.3 and its explicit maps (pp.74–75), and Lemma 4.4.10 / Proposition 4.4.11 (pp.158–159). These statements are about arbitrary simplicial sets; there is no Stacks tag to compare, and no SGA source was used. The item's left/right horn ranges and absence of fibrancy assumptions match its source. The cancellation node matches its separate corollary hypothesis by hypothesis.

- Step 1: checked against the three cited definition statements and the saturation paragraph of Proposition 4.4.11; PASS after spelling out the pushout attaching map, the restriction of the left fibration at each chain stage, and all four maps of the arrow retract. The argument uses degreewise fibers and the stated closure operations, without assuming the conclusion.
- Step 2: checked the new cancellation statement on the monomorphisms E_A → E_B → E; PASS. E_B → B is a left fibration by Step 1, and the composite is the pullback of gf, so both right-anodyne premises actually hold.
- Step 3: checked the actual right-anodyne pushout-product statement, the horn-lifting definition and lem-coef-transfinite-left-lifting; PASS. Opposite order changes horn index i to n−i and endpoint 0 to 1. Pushout and retract lifting are direct square manipulations; the transfinite part is precisely the cited Mathlib leaf. Read its declaration in TransfiniteCompositionLifting.lean:265–273.
- Step 4: checked against Step 3, the cited degreewise simplicial conventions and left-fibration definition, and the homotopy in Proposition 4.4.11; PASS. The max map commutes with restriction of simplices, both prescribed lifts agree, and its endpoint gives the asserted strict retraction relative to K.
- Step 5: checked against the product node's exact pushout-product formula and the right-anodyne retract closure, alongside Lemma 4.4.10; PASS. The right-anodyne prism uses endpoint 1, and the section of the arrow retract uses endpoint 0; all square and composite identities are explicitly present.
- Step 6: checked against Steps 1, 2 and 5; PASS. The map from {1} × B to D is the displayed pushout of e_A, and its composite with P(a) is e_B. This is an elementary use of the proved cancellation property and needs no new generating-criterion node.
- Step 7: checked against the cited monotone-simplex/horn statement and the first half of Lemma 3.1.3; PASS after writing the branchwise and cross-branch monotonicity inequalities and the precomposition check. An image can add only vertex k, while the endpoint-1 image misses 0; hence the restrictions really define both arrow squares.
- Step 8: checked against the minimal closure in the cited right-anodyne definition and Steps 1 and 7; PASS. The conclusion applies directly to the given q, without a Kan or quasicategory premise.
- New node lem-coef-right-anodyne-mono-cancellation: checked against Corollary 4.1.10, the existing DAG statements and Mathlib; PASS. It is statement-only, self-contained, has both definition dependencies, single-escaped TeX, precise source numbering and complete blueprint ancestry. It is independent cancellation for composable monomorphisms, not a clause or restatement of base change. Whole-DAG searches for the source number and right-anodyne cancellation found no duplicate; the existing saturation, product, contravariant-model and spine-cancellation statements do not supply it. Four fresh msearch.py queries are appended verbatim to its search records. Loogle returns ordinary/inner-anodyne closure facts, LeanFinder returns horn face identities and the all-horn Kan generator, broad grep finds the all-horn/inner files and targeted one-sided names grep finds nothing. Read AnodyneExtensions/Basic.lean:63–93 and CategoryWithFibrations.lean:35–106; none matches in one line. No new Mathlib leaf is justified.

Edge cases: independently enumerated all 3,309 nondegenerate prism chains for 1 ≤ n ≤ 5 and every 0 < k ≤ n, checking monotonicity, rs = identity and the horn-image condition; all passed. At n = k = 1 the retraction on the final endpoint is constant at 1. Empty T gives identity on the empty simplicial set; K = E gives the prescribed identity lift on the entire cylinder. Cancellation permits identity maps and empty simplicial sets, and imposes no dimension-zero horn or nonemptiness assumption. No statement dispute was found. Independent project-source searches found no one-sided-fibration/anodyne declaration to attach; upstream master sorries are not treated as proofs.

Changes made and reasons:

- Expanded Step 1's pushout, chain and retract calculations so the saturation claim is reviewable directly from definitions (C2, E5).
- Expanded Step 7's monotonicity and naturality checks so the poset formulas give explicit simplicial maps (C2, E5).
- Added four actual independent Mathlib searches to the cancellation node and retained the complete search log; no declaration matched.
- Checked all 13 citation records against the current sandbox/reference node statements: every quote remains verbatim, and the proof-dependency union is exact. The repaired steps use the same cited facts, so citations.json needs no change.
- Retained both mathematical statements, the one necessary new unsplit node, and all first-worker report sections. The required server dry run and push follow this completed second-reading section.
