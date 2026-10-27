# Q78: lem-sfb-split-positive-root-borel

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-split-positive-root-borel.json`: statement, split into eight proof steps; Mathlib verdict: no matching group-scheme theorem. Statement and statement dependencies unchanged.
- `citations.json`: twenty verbatim cited-statement quotations, one for every step/node pair.
- `report.md`: this report. `searches.jsonl` is the unmodified log produced by the required search command.

New nodes: 0. New Mathlib leaves: 0. All supporting statements already exist. No Lean files, repository files, launcher files, compilers or build tools were written or invoked.

## Attachments

`AlgebraicGeometry.Scheme.Modules.finitePresentation_projective_sections` belongs to `lem-pc-finite-flat-affine-sections-projective`, already recorded there with slopmaster2 state closed. I read `lean/WeilConjectures/AlgebraicGeometry/Modules/LocallyFreeAffine.lean:67` through the end of its proof at line 109: it gives exactly the finite-presentation and projectivity assertion used as a generic tool in step 2. No attachment change is requested.

The item's id and Borel/positive-root/pinned-split concepts have no matching project declaration under `lean/WeilConjectures/`; the lone positive-root prose hit concerns a root chart of a curve, not reductive groups. Consequently the item is not an ATTACH claim.

## Wanted literature

WANTED: Brian Conrad, *Reductive group schemes*, local file `literature/conrad-reductive-group-schemes.pdf`, Theorem 4.1.7, Theorem 5.1.13 (printed pp.143-144), Proposition 5.2.3 (pp.152-153), Corollary 5.2.7(2) (p.155), Remark 6.1.2 (p.186), for lem-sfb-split-positive-root-borel. I read the author's PDF at https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf online; no document was downloaded. The proof is conservatively marked agent-written because its explicit assembly and tangent calculation are mine and the human document is not locally available. No SGA source is used.

## Findings and changes

The imported item was an unsplit, statement-only supporting lemma created by Q56. No earlier sandbox item, report, citations or searches existed at the start. There is no repair note for this item. The live statement agrees with Conrad's positive-system construction and was retained verbatim; no STATEMENT-DISPUTED claim is needed.

The existing relative root-product theorem is restricted to Noetherian local rings and the existing root-exponential/tangent-weight theorem assumes Noetherianity. Neither can prove this arbitrary-ring item as stated. Instead I reused the existing arbitrary-ring dynamic-subgroup theorem and geometric regular-cocharacter theorem, and wrote out their assembly. I did not add a new node for an arbitrary-ring version of the old root-product theorem, or for any clause of this item. In particular, I avoided hiding uniqueness in a new “positive Borel uniqueness” node.

I read the chapter and unit records and the newest blueprint under `literature/blueprint/latest` (main-20261024, ef6f9619), including the direct-images proof and current unit and chapter sections. This item remains the inherited lower-level reductive-model prerequisite of the direct-image route; it does not replace a chapter or unit step. `tools/blueprint_refs.py ancestor` reports the existing null blueprint ancestor, which I preserved with its detailed inherited place and via chain. Whole-blueprint searches for “Borel”, “positive root”, and “cocharacter” found no equivalent subgroup-scheme statement. DAG and source searches found all the tools now cited. No node was created, so no new duplicate pairs need resolution.

Fresh logged searches used LeanFinder with two mathematical phrasings, Loogle, LeanSearch, and grep. They returned abstract root pairings, Lie-algebra constructions or measurable Borel spaces, not a theorem about Borel subgroup schemes over a ring. All services answered; none was recorded as unavailable or silently replaced. Existing item search records were retained and the five actual new log records were appended without changing tool or query text.

## Unfinished work

None within stage 1. Lower-level cited nodes retain their existing independent stages and statuses; I did not change them. The unit key theorem and its realization fields are not this item.

## Not duplicates

No new nodes. Existing `lem-sfb-relative-root-product-open-cell` has Noetherian-local hypotheses, and `lem-sfb-local-borel-quotient-geometry` starts from a given Borel over a Noetherian local ring. Neither is silently applied outside its hypotheses here.

## Review by Q78

I read Conrad's actual dynamic proof of Theorem 5.1.13, the proof of Proposition 5.2.3 and Corollary 5.2.7(2), and the warning about disconnected bases in Remark 6.1.2. The latter is significant: arbitrary Borel subgroups on different connected components need not come from one constant positive system. This item's fixed weight set does impose that constant positive system; the proof never asserts that all Borel subgroups arise from one. For the cotangent calculation I also read Stacks Tag 02G1, `morphisms-lemma-smooth-omega-finite-locally-free` at `morphisms.tex:7214`, and Tag 00RV, `algebra-lemma-differentials-base-change` at `algebra.tex:34213`, and the existing affine-sections Lean theorem mentioned above. There are no new nodes requiring additional source readings.

I opened every cited node and checked the following uses against its statement (not a proof hidden inside it):

1. `def-sfb-pinned-split-root-realization` supplies the rational independence and same-sign integral expressions of the base; `def-sfb-ring-diagonalizable-group` supplies exactly the Hopf character maps. Extending a rational basis and clearing its finitely many denominators constructs the required integral cocharacter explicitly, even if the roots do not span the entire character space. This is an elementary step, not a new root-system lemma.
2. `sbc-lem-smooth-relative-dimension-locally-constant` explicitly states finite local freeness of the smooth differential module (in its Tag 02G1 clause). `lem-pc-finite-flat-affine-sections-projective` supplies finite projectivity over the affine base. `lem-weil-pbc-kahler-differentials-base-change` is an arbitrary-ring, arbitrary-map isomorphism, not a flat-map result. `lem-sfb-relative-torus-bundle-weights` gives weight decomposition and arbitrary base change for finite projective modules. The derivation and dual-basis computations in the step explain their application to tangents. Both off-unit generic tools are declared in split_report.tool_uses; the two other inputs are respectively a Mathlib leaf and an in-unit theorem.
3. `lem-sfb-relative-dynamic-subgroups` has precisely smooth affine finite-presentation hypotheses over any ring, and explicitly supplies closedness, smoothness and the nonnegative tangent formula. The definition of the pinned realization supplies these hypotheses and its actual root-line decomposition. This proves the constructed subgroup's weights, rather than assuming a Borel already exists.
4. `lem-sfb-pinned-split-root-base-change` explicitly handles nonflat maps and preserves the same abstract roots. The dynamic theorem commutes with arbitrary base change. `lem-sfb-regular-cocharacter-borel-description` applies over the algebraically closed geometric field, with the specified maximal torus and regular integral pairing. I checked that a root pairing equal to a multiple of the characteristic does not become zero: regularity is integral and is not defined by differentiating characters.
5. The competing subgroup Q is affine because closed in the affine G, and smooth affine over the affine base, hence finitely presented; no finiteness of its defining ideal was assumed without this reasoning. Its full torus weight decomposition has no negative lambda-degrees. The dynamic theorem gives equality of tangent modules for P_a(Q) -> Q, and step 2 transfers the differential to every geometric fibre. `lem-sfb-smooth-subgroup-tangent-generation` says exactly that one smooth connected closed subgroup with the full tangent space is the whole connected smooth affine geometric group. The dynamic theorem supplies connectedness, and Q's fibres are Borel, hence connected. `lem-sfb-flat-geometric-fibre-open-criterion` then turns the fibre isomorphisms into a scheme isomorphism, with smooth finite-presentation source and target. There is no appeal to equality of geometric point sets over a nonreduced ring.
6. The factorization into B is written as a composition of each extending orbit, on every algebra; the affine quotient description proves it is a closed inclusion. Borel maximality in the geometric fibres now gives equality there. The same fibre-isomorphism theorem applies to Q -> B, whose source and target are smooth affine finitely presented. This proves the actual uniqueness clause.
7. The base-change theorem for pinned realizations and dynamic-subgroup theorem both state the arbitrary-map compatibility used. For a pinned isomorphism the displayed conjugation identity and its inverse carry orbit extensions both ways, so the image subgroup is identified explicitly before using uniqueness. No unspecified transport argument is left.
8. The regular-cocharacter theorem explicitly includes empty roots and T=G. Together with the same fibre criterion this proves T=G over the ring; the constant-orbit definition gives B=G on all algebras.

I tested rank zero and pure split tori, SL2 over fields of characteristic 2 (the root remains a nonzero character even though its differential can vanish), dual-number base rings, nonflat specialization, product rings with disconnected spectra, and arbitrary central torus factors. A mixed upper/lower SL2 Borel over a product ring has both root signs globally and fails the stated constant positive-weight condition, as it should. None of these tests requires an added hypothesis or weakens the conclusion.

I checked B1-B10 (self-contained existing statements, no new-node proof or duplicate, actual search records), C1-C8 (every substantive fact has a stated citation, tool uses declared, no dependence on the item through these tools), D1-D5 (the steps construct and prove the item rather than relabel its clauses), and E1-E7 (hypotheses, objects, nonflat maps, nilpotents, and explicit compatibility). Every proof step is below 2000 characters; the elementary steps are calculations from their cited statements. `citations.json` copies each cited statement verbatim. The preliminary server review_split check passed with zero new nodes before the final full dry run.
