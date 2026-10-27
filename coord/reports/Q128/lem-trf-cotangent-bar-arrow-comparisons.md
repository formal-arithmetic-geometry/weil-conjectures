# Q128 stage-1 report: lem-trf-cotangent-bar-arrow-comparisons

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-cotangent-bar-arrow-comparisons.json`: statement split into six complete steps; no statement changes; no new nodes; no Mathlib leaves.
- `citations.json`: sixteen step/node entries, each quote checked literally against the current cited statement.
- `searches.jsonl`: six actual logged searches (two LeanFinder phrasings, Loogle, LeanSearch, and two Mathlib greps). Inherited searches remain in the item unchanged; the fresh searches are appended with their actual query strings and digests.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, cotangent/bar terminology, and cotangent functoriality. The returned declarations concern cotangent spaces, local smoothness, and individual presentation complexes; none supplies this item's complete assertion. No Lean source was written or compiled.

## WANTED

None.

## What was wrong or missing

The item was statement-only, with no proof. Its statement is mathematically correct, including both directions of the natural transformations after taking opposites. I retained it verbatim, together with all provenance and inherited searches.

Stacks cotangent Tag 08QL explicitly omits agreement of its two descriptions of functoriality. The existing `lem-trf-cotangent-sheaf-model` now states that agreement, for arbitrary ring squares, so the proof cites its statement rather than using the omitted verification as an elementary assertion. Likewise `def-trf-derived-colimit-bar-system` defines a type of data but does not assert inhabitation: the proof uses the theorem `lem-trf-derived-colimit-bar`, which actually supplies the generator maps and prism equality. Stacks 08Q8 has an ill-typed functor order and a right/left-adjoint typo; the existing change-of-rings node already corrects these. This item uses that node's typed statement and explicit normalized comparison, not the erroneous printed formula.

No new statement dispute or route change is needed. The inherited blueprint ancestor is `lem-trf-local-term-locality`; its current main-20261015 update is a contracting-correspondence statement. This cotangent item is a historical auxiliary input along the recorded long support chain, not a new realization of the unit's main proof. I leave the chapter and unit records untouched.

## Not duplicates

No new nodes. Existing statements suffice, especially `lem-trf-derived-colimit-bar`, `lem-trf-cotangent-sheaf-model`, and `lem-trf-bar-scalar-unit-transpose`. Whole-blueprint searches for “cotangent”, “functoriality”, “bar prism”, and “prism homotopy” found no second statement of this item. DAG searches for 08QL/08PH, prism homotopy, scalar adjunct, and the derived coefficient adjunction found these existing general tools, which are reused.

## Review by Q128

I read the item and all its statement dependencies. For the item I read Stacks `cotangent.tex`, Tag 08QL (`section-functoriality`, lines 867–960), including the two maps on standard resolutions and the presentation-category functor, and Tag 08QU (`lemma-triangle-ses`, lines 1173–1221), including the differential maps and base-change identification. I also read `sites-cohomology.tex`, Tags 08PG and 08PH (`example-left-derived-colimits` and `example-morphism-categories`, lines 10044–10172), the derived coefficient adjunction at 07A6 (`lemma-adjoint`), and the printed change-of-rings formula at 08Q8. There are no new nodes requiring additional sources.

Step 1 uses the differential-presheaf statement for the actual categories, presheaves, restriction maps and generators, and the Kähler-differentials definition for its generator/relations presentation. I checked naturality before reversing arrows: the equation for the first transformation is compatibility of a pair map with P to Q, and for the second it is equality on q tensor b in the quotient tensor product. These are algebraic equalities for arbitrary maps. Polynomiality is immediate from A[x] tensor_A B = B[x], including empty and infinite variable sets; the common size convention is already part of the cited setting. No extra flatness is used.

Step 2 uses exactly the natural-transformation conclusion of the bar theorem with v=u_2 and w=h_1u_1. Its coefficient map is the actual a_U: on (dp tensor r) tensor c both give d(iota(p)) tensor beta(r)c. The term-identification statement names the canonical bar reindexing c_i and explicitly specifies how the first scalar tensor fits. Thus the two prism endpoints are the two claimed composites, not just maps with the right source and target. The equalities are in D(C), as the bar theorem states.

Step 3 uses the same three cited statements with v=u_3 and w=h_2u_2. I checked the often missed coefficient face: restricting along the opposite arrow is induced by Q tensor_A B to Q tensor_P B. The third differential identification in the cited exact-sequence statement sends d(q tensor 1) to the relative differential d_{Q/P}q, exactly b_U. It does not invert the generally noninvertible quotient map. This verifies the hypothesis of the bar theorem and both endpoints for the second equality.

Step 4 uses the sheaf-model statement's final displayed naturality equation, which is stronger than merely giving an isomorphism of objects. Applied to (A to C) to (B to C) it gives the second standard arrow. Applied to (A to B) to (A to C) it gives the B-semilinear first arrow; the bar theorem's natural-isomorphism clause removes P tensor_A A using p tensor a to ap. The coherence statement identifies exactly which standard maps these are. I checked base and coefficient rings separately; the first equality at this stage lies in D(B) with target restricted along B to C.

Step 5 uses four existing statements: the term-identification lemma gives flatness of every F_1(P); the objectwise-flat bar lemma gives K-flatness and flat terms of Y and F_1[0]; the bar scalar-unit-transpose lemma identifies the adjunct of j with Phi inverse for the representative-normalized adjunction; and change of rings identifies this Phi with the scalar comparison used in alpha_1. The equality Tj=gamma holds on every bar generator. Naturality of the adjunction bijection in source and target then transposes the equation from step 4; this is the defining naturality of an adjunction, not a new derived-functor comparison. This produces theta T = f(theta tensor 1)Phi with the direction of Phi checked. The tensor generator rule multiplies beta(r)c; it does not assume B to C is injective or flat.

Step 6 substitutes the explicitly stated alpha formulas from the term-identification node in the preceding equalities. It is associative composition only and requires no extra theorem. Every cited node's statement was opened and checked; citations.json quotes those statements literally. The proof depends on the cited nodes as theorems, including unsplit ones, rather than on their internal proofs. No hidden lemma is being moved to a new node. All steps are shorter than 2000 characters.

Small cases checked: A=B=C (both transformations may contain identity arrows, allowed by the bar theorem); no polynomial variables (differential modules are zero); arbitrary infinite variables (all individual differential expressions and direct-sum elements have finite support); B to C a quotient such as Z to Z/2 (the scalar adjunct is derived and uses flat F_1 values, not flatness of C); and zero target ring (all C-module maps vanish). The second quotient tensor is never claimed invertible. These checks agree with all stated hypotheses.

For Mathlib I read the returned hits and source at `Mathlib/RingTheory/Extension/Cotangent/Basic.lean:53–65,250–275` and `Mathlib/RingTheory/Kaehler/Basic.lean:650–674`. Mathlib's cotangent complex there is the conormal-to-differentials map of a single presentation. Its map homotopy is not the derived polynomial-presentation comparison here. The second semantic search returned Dold–Kan homotopies; I inspected `DoldKan/HomotopyEquivalence.lean:60–87` and `Algebra/Homology/Homotopy.lean:241–255`: these construct different homotopies or the general hd+dh map, not the cotangent/pair-site comparison. Accordingly all fresh searches have verdict no match, not Mathlib leaf. No unrun query is recorded.

I checked delivery-errors B–E: no new-node forms to validate, literal TeX and provenance retained, no relabelled clause nodes, no dependence on a definition for an existence theorem, every substantive comparison is supplied by a cited statement, and both ring-square and prism hypotheses are verified above. The actual review_split and final delivery preflight results are recorded by their tools below the sandbox workflow; no local copy of those checkers was run.

## Unfinished work

None in the one-level split. The dependencies remain independent DAG tasks; no claim is made that their Lean proofs are complete. Delivery is subject to the required server checks and maintainer review.
