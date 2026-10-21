# Worker report: lem-coef-direct-image-hom-evaluation-square

Group Q88; stage 1 only; 2026-10-21. Direct delivery, independently reviewed by the maintainer after push.

## Files written

- dag/nodes/sec-six-functors/lem-coef-direct-image-hom-evaluation-square.json: statement, split into six steps; no exact Mathlib match.
- citations.json: six entries containing verbatim portions of the four existing cited statements.
- report.md: this report.
- searches.jsonl: maintained by the required msearch.py command, with the actual five searches performed for this item.

There are zero new nodes and zero new Mathlib leaves. Existing metadata and searches were retained. The item had no sandbox node or previous split/report on arrival, so there was no existing dry run to resume.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for direct-image/Hom/evaluation/scalar combinations, and read the relevant MonoidalProjectionConjugate and coefficient-change search hits. No project declaration states this entire two-coefficient ordinary unbounded evaluation equation. In particular an ordinary restriction/coextension unit formula or a comparison for a completed pro-etale coefficient category is not an attachment for this item.

## WANTED

None. All documents needed for this formal calculation are available locally.

## What was wrong or incomplete

The statement was correct and the item had an empty proof. Its claimed generality requires using ordinary unbounded module categories throughout. The statement remains unchanged. In particular the scalar extension of an internal Hom, the geometric direct-image scalar comparison, and b are arbitrary morphisms and are never inverted. Only the canonical pullback and tensor comparison isomorphisms are inverted.

The detailed blueprint source inherited by this extracted node is literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/thm-coef-finite-hom.md, especially paragraphs 1 and 4. I also read the current main-20261015 copy at sec-smooth-purity/sk-lem-sp-tower/thm-coef-finite-hom.md: it retains the same evaluation/adjunction-compatibility claim but does not include the detailed proof. I retained the inherited source rather than pretending that the current file contains a proof it omits. The unit and chapter records were read; this is an auxiliary calculation below their biduality route, not the unit's key statement. No unit or chapter file is changed. No SGA source or exceptional pullback theorem is used.

## Unfinished work

None in the stage-1 split. No Lean was written, no compiler or build tool was run, and no claim of formal proof completion is made.

## Not duplicates

No new node was created, so there are no new/existing node pairs. DAG searches by evaluation, counit, transpose, scalar and internal-Hom terminology and blueprint_refs.py searches for evaluation, adjunction, counit, direct-image.*evaluation and scalar.*evaluation were read. The existing lem-pod-closed-uncurry-laws supplies a left-tensor convention, while the item's evaluation has right tensor by L; I instead reused the existing right-tensor closed-structure definition def-coef-ringed-tensor-hom-model. The completed finite-free scalar compatibility lemma is in a different coefficient category and is unnecessary. General adjunction identities and the final naturality substitution are steps, not new nodes. The parent lem-coef-internal-adjunction-pairing-change was read for the exact ordinary-counit clause it needs; it is not cited back, avoiding a cycle.

## Mathlib search reading

Ran the required msearch.py leanfinder, loogle, grep and leansearch calls and a second leanfinder phrasing. Each query is copied unchanged to the item's mathlib_searches; previous inherited searches remain. All services returned hits, so none is described as unavailable. Read Mathlib CategoryTheory/Adjunction/Basic.lean (226-245), Monoidal/Closed/Basic.lean (160-205), and Monoidal/Closed/Functor.lean (42-86). Hom-bijection naturality and uncurry-curry identities explain the formal reductions. expComparison_ev has Cartesian monoidal hypotheses and is not a specialization to the module derived tensor. The light-condensed and underived module hits do not state this geometric derived two-coefficient square. The item therefore remains a split statement, rather than a Mathlib leaf.

## Review by Q88

I checked the statement and each step against the actual statements of every cited node, not their proofs. For the item I read the blueprint evaluation definition in paragraph 1 and the instruction to transpose the comparisons in paragraph 4. I checked the foundational comparison in Stacks sites-cohomology.tex, Tag 07A4 (lemma-pullback-tensor-product, including its bifunctoriality and K-flat construction), Tag 0D6D (lemma-derived-pullback-composition), and Tag 07A6 (lemma-adjoint). I also read the existing right-tensor closed model and scalar-Hom adjunction statements. No new source or unsplit auxiliary lemma is being introduced: the remaining argument consists of the axioms of those adjunctions and functor/natural-transformation laws.

Step 1 uses lem-weil-pbc-ringed-topoi-derived-tensor-pullback for the natural tensor comparison, applied to the identity geometric morphism and the coefficient ring map. It uses lem-sfb-ringed-derived-monoidal-comparisons for composition and the specified 2-isomorphism comparison between the two scalar/geometric factorizations. That statement explicitly covers arbitrary structural ring maps, unbounded inputs and monoidal pullback comparisons. The constant coefficient square is a square of ringed topoi because inverse image carries the constant ring to the corresponding constant ring and both structural maps are induced by A to B. I wrote the exact factorization iota=(a inverse tensor 1) mu so the inverse orientation can be checked. These two nodes are declared as generic tool uses in split_report; they do not replace a unit-level route.

Step 2 takes the ordinary adjunction and counit from def-kun-projection-formula-map; that definition explicitly supplies them on unbounded small-etale module derived categories, without geometric finiteness assumptions. The equation for t is cancellation of the defining adjunct/inverse-adjunct bijections. No additional coefficient compatibility theorem is smuggled into this step: c was defined using exactly this inverse adjunct in the item itself.

Step 3 uses the same adjunction. Its counit is a natural transformation by definition of adjunction, so I wrote its naturality equation at w and expanded h. This is two-line categorical algebra, marked elementary, not an application of a theorem about invertible base-change comparisons. Domain checks: w goes from FQ to H prime and the resulting inverse adjunct goes from P_B F_X T to H prime.

Step 4 cites def-coef-ringed-tensor-hom-model exactly for right tensor by L being left adjoint to H(L,-), with evaluation as its natural counit. The first equation is inverse-transpose cancellation for u, and the second is counit naturality at arbitrary b. Substituting w gives the displayed evaluation equation. Thus a definition is used only for the structure and its defining laws; no existence or comparison theorem is attributed to a definition. The canonical tensor-Hom structures invoked here are already part of the item's conventions (lem-sfb-dc-hom-scalar-adjunction); the step simply spells out their evaluation normalization. Unlike the left-tensor Mathlib leaf, this definition has exactly the needed tensor ordering.

Step 5 cites the actual bifunctoriality clause of lem-weil-pbc-ringed-topoi-derived-tensor-pullback at d and the identity of L. I wrote its equation and multiplied by the two tensor comparison inverses. This verifies precisely the often-hidden tensor-transport step, with no implicit reassociation of a noninvertible map.

Step 6 cites no further node: it is the displayed substitution of the previous five equations, functoriality and inversion of Step 1's factorization. Both sides have source P_B F_X T tensor_B F_Y L and target N prime. The final e_A is the very composite defined in the statement. Every proof step is below 2000 characters; none hides a separately stated lemma.

I checked the B--E delivery-error cases individually: no new statement-only nodes are needed (B1--B9); no exact finished attachment was found (B10); every non-elementary input appears in uses, with the exact supplying statement checked and quoted (C1--C5); no parent is cited and no new cycle is introduced (C6); the foundational cross-unit tools are explicitly declared (C7--C8). The calculation itself carries the argument rather than moving any clause to a new node (D1--D5). Small cases checked algebraically: f equal to the identity makes c and the ordinary counits identities and leaves the defining u/b evaluation equation; A=B makes u the identity and the claim is ordinary counit naturality followed by evaluation naturality; b=0 makes both sides zero; L=0, N=0 or N prime=0 gives the unique zero pairing; the empty site and the zero coefficient ring are included. Taking a nonflat quotient such as Z to Z/2 changes no step because all tensors are derived. No properness, finite-Tor, constructibility, boundedness or invertibility of b is used (E1--E7).

All six quotes were checked as literal substrings of the corresponding live node statements before writing citations.json. The repository was read only; all written files are in the assigned sandbox.
