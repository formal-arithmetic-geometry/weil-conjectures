# Stage-1 repair: lem-coef-cartesian-simplex-inverse-extension

Q63, 2026-10-17. This repairs the returned long-step split while keeping the item statement and Lean record unchanged.

## Worker report

Files written:

- `dag/nodes/sec-six-functors/lem-coef-cartesian-simplex-inverse-extension.json`: item, fifteen proof steps.
- `dag/nodes/sec-six-functors/lem-coef-infinity-equivalence-cancellation.json`: statement-only unsplit node; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-infinity-cocartesian-image-criterion.json`: statement-only unsplit node; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-infinity-equivalence-preserves-cocartesian-edges.json`: statement-only unsplit node narrowed to essential-image test transport; no Mathlib match.
- `citations.json`: 36 verbatim step/node quotations.

Attachments: none. No declaration in either named source checkout states the item or any of the three new nodes without `sorry`.

WANTED: Lurie, *Higher Topos Theory*, Proposition 2.4.4.3 and Proposition 3.1.3.5. The cached `HTT.txt` and `HTT.pdf` in this sandbox were read; no document was downloaded.

The returned item had a 2040-character non-elementary step 10. The previous extraction grouped its image-test and arbitrary-test arguments in one broad node. This repair makes each substantial hidden argument a separate statement node and cites it from a separate short step. The item statement, `stmt_deps`, source, Lean records and steps 1–9 remain unchanged. Step 11 still performs the opposite-category setup. Step 14 applies the mapping criterion after all test vertices are covered, and step 15 is the marked-cylinder conclusion. No statement was corrected or disputed.

## Sources and blueprint

I read the cached HTT text at lines 7651–7702 (Proposition 2.4.4.3 and its coherence warning) and lines 9011–9112 (the simplex construction in Proposition 3.1.3.5), together with Corollary 2.4.4.4. The item follows the specified-boundary $n>0$ route: mapping-cylinder pushouts, Joyal homotopy extension, automatic compatibility with the simplex nerve, and the marked mapping-square check. The nearest blueprint ancestor is `prop-coef-integral-exceptional-adjoint`, proof paragraph 2; all three new nodes carry that ancestry and the existing `via` chain. Whole-blueprint searches for equivalence-over-base preservation, cartesian/cocartesian mapping squares and the cited HTT place found no duplicate.

## Proof extraction

Step 10 uses `lem-coef-infinity-equivalence-cancellation`: from $rf\simeq1_X$ and the already established categorical equivalence $f$, Joyal two-out-of-three gives that $r$ is an equivalence, hence fully faithful and essentially surjective.

Step 12 uses `lem-coef-infinity-cocartesian-image-criterion`: on opposites, full faithfulness over the common base gives the top mapping-space equivalences, coherent Hom functoriality gives the whole square with its commutation data, and pullback recognition transfers the criterion to every image test vertex.

Step 13 uses `lem-coef-infinity-equivalence-preserves-cocartesian-edges`: essential surjectivity supplies $Tz\to w$; coherent postcomposition by this equivalence and its base image, with inverse and composition homotopies, transfers the criterion square from $Tz$ to arbitrary $w$.

Step 14 invokes the existing cocartesian mapping criterion for all test vertices and reverses the initial-horn condition. Step 15 uses the marked triangle generator and the relative sharp mapping-complex definition. No substantial argument remains under an elementary label, and the longest non-elementary step is 1131 characters.

## Not duplicates

lem-coef-infinity-equivalence-cancellation vs lem-coef-joyal-quasicategory-characterizations: the existing node characterizes a single functor's equivalence; the new node is the cancellation consequence using $rf\simeq1_X$ and two-out-of-three.

lem-coef-infinity-cocartesian-image-criterion vs lem-coef-infinity-cocartesian-mapping-criterion: the existing node characterizes one edge by its mapping squares; the new node compares the entire criterion square under a fully faithful functor over a base.

lem-coef-infinity-cocartesian-image-criterion vs lem-coef-infinity-hom-bifunctor-functoriality: the existing node gives coherent Hom naturality for arbitrary functors; it does not state the cocartesian criterion or pullback conclusion.

lem-coef-infinity-equivalence-preserves-cocartesian-edges vs lem-coef-infinity-cocartesian-mapping-criterion: the existing criterion has no essential-image transport conclusion.

lem-coef-infinity-equivalence-preserves-cocartesian-edges vs lem-coef-kan-nerve-pullback-recognition: the existing node transfers cartesianness of whole space-valued squares; it does not construct the equivalence of quasicategorical criterion squares from an essential-image equivalence.

lem-coef-infinity-equivalence-preserves-cocartesian-edges vs lem-coef-cartesian-simplex-inverse-extension: the item constructs an exact-boundary inverse and marked homotopy; the new node only transports a criterion for an already given equivalence and edge.

I searched the complete DAG, the blueprint and both named project source trees for these statements and their declaration names. No attachment or more general existing node states any of the three new arguments. Their dependency closures do not return to the item.

## Mathlib searches

For every new node I ran LeanFinder, Loogle and scoped Mathlib grep, then a second phrasing before recording no match. Cancellation searches found only ordinary-category `Functor.isEquivalence_of_comp_left/right` and related results. Image-comparison searches found ordinary `IsCocartesian.map` and square `IsPullback` results. Essential-image transport searches found ordinary cocartesian isomorphism and pullback transport. None states a horn-cocartesian result for quasicategories with right-pinched mapping spaces, and none specializes in one line. The exact tool queries and raw responses are retained in `searches.jsonl` and each node's `mathlib_searches`; unavailable services were not treated as negative evidence.

## Review by Q63

I reopened every cited node used in steps 10–15 and checked the hypotheses at the point of use. Step 10 has the categorical equivalence $f$ from step 3 and the coherent equivalence $rf\simeq1_X$ from step 9; the cancellation node supplies exactly the resulting equivalence, full faithfulness and essential surjectivity. Step 11 uses the opposite-quasicategory clause and the horn definitions: order reversal exchanges final and initial horns, and the equality $q_0T=p_0$ is strict from step 9. Step 12 has inner fibrations on both opposites, strict common-base equality and full faithfulness; its cited image node supplies a comparison of whole coherent squares, so the pullback conclusion is not inferred from four unrelated edge classes. Step 13 has essential surjectivity from step 10; its cited transport node explicitly includes an equivalence $Tz\to w$, its inverse, the base image and coherent composition homotopies, so arbitrary target vertices are covered without assuming vertexwise surjectivity. Step 14 applies the existing criterion only after this transport and reverses the horn definition. Step 15 checks every marked product edge, including degenerate edges, using the cited marking generator and the exact boundary restriction from step 9.

For steps 1–9 I reread the retained source and statements: the relative marked calculus supplies the pulled-back fibrations and natural markings; the cartesian mapping-fiber and homotopy-fiber nodes handle empty base mapping spaces; the face induction uses the cofibrant-span hypotheses and monomorphic legs; the two cobase changes use all-cofibrant left properness; the prism and model homotopy-extension nodes provide the exact extension; and vertex determination applies because the base is $N([n])$. The boundary is never treated as a quasicategory.

I tested the new statements on identity equivalences, a point base, empty total categories, and a two-object contractible groupoid equivalent to a one-object skeleton. I also checked the item's $n=1$ case and allowed non-injective $f$; $n=0$ remains excluded by the item. The three new nodes are statement-only, have complete definition dependencies, no hollow data and no unearned Mathlib status. `proof_deps` is exactly the union of step uses, and `citations.json` contains one verbatim quote for every use. No cycles, source attachments or blueprint duplicates were found.

## Unfinished work

The three extracted statements are intentionally unsplit and ready for their own stage-1 workers. The required dry run is the next validation step; no Lean, compiler, Lake, local checker or live-project write was used.
