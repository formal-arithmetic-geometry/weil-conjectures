# Stage-1 report: lem-trf-generic-rank-admissible-invariance

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-generic-rank-admissible-invariance.json`: six-step split, unchanged statement; not a Mathlib leaf.
- `citations.json`: verbatim statement quotations for all 15 step-to-node citations.
- `report.md`: this report. No new nodes, no new Mathlib leaves, no Lean files.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact item id and the notions `generic.rank`, `admissible.invariance`. The generic-rank module concerns a single integral scheme; it does not give the relative rank function or the admissible-transform assertions. The existing closed `lemma-nagata-admissible-blowup-over-open` remains its existing attachment; I only cite it.

## WANTED

None. All needed literature is present.

## What needed repair

The imported item had a statement and searches but no proof. Its statement is correct; no correction or STATEMENT-DISPUTED is needed. The implicit argument in Stacks 0811 that generic rank is locally constant is now explicit: an open free neighbourhood has open image, and any nonempty open in an integral fibre contains its generic point. This concerns the rank of the stalk after tensoring with its residue field, not the rank of a module already flat at every point of the total space.

All invariance assertions use successive module strict transforms on the base-changed total spaces, with each actual centre retained. The proof does not assert that the module is globally flat, or that a strict transform depends only on the blowup morphism.

## Mathlib and duplicate searches

The inherited 2026-10-22 searches were retained. New searches through the required msearch command on 2026-10-23 used LeanFinder twice, Loogle, grep and LeanSearch; their exact queries and actual hit lists are recorded in the item and `searches.jsonl`. Both phrasings return rank-at-stalk/free-locus results, not the relative statement. I read `Mathlib/RingTheory/Spectrum/Prime/FreeLocus.lean`, especially lines 186--229 and the rank-base-change declaration at 322. Those results concern one finitely presented module over one ring, not the function taking a base point to the rank at the generic point of its fibre; they also have no strict-transform conclusion.

Searched the whole DAG for Stacks 0811/080Y, generic fibre rank, strict transforms, generic freeness, flat open maps, base-change stability, the generic-point field, and affine permanence. Existing nodes supply every needed lemma, so none was created. Whole-blueprint searches for `generic rank`, `080Q`, `admissible invariance`, and `generic fibre rank` were made with `tools/blueprint_refs.py search`; the ancestor command confirms `lem-trf-local-term-locality`. Read the current `literature/blueprint/latest/` locality proof and unit text. The inherited flattening subroute and ancestor/via attribution are retained; this split changes no chapter or unit route.

## Not duplicates

No new nodes. Existing lemmas were cited instead of introducing special cases or separate nodes for clauses of the item.

## Review by Q79

I read the item against `literature/stacks-project/flat.tex`, Tag 0811 (`lemma-flatten-module-pre`), its hypotheses and first two proof paragraphs, and Tag 080Y (`remark-successive-blowups`). I also read Tag 080Q (`lemma-flat-and-free-at-point-fibre`) in `more-morphisms.tex`, including its explanation about a reduced fibre's generic local ring being a field, and the base-change/open-map source statements in `morphisms.tex` (01SD, 01TS, 01U9, 01UA). For strict transforms I read `divisors.tex`, `definition-strict-transform`, `lemma-strict-transform`, and `lemma-strict-transform-flat`, checking that centres matter. No SGA source is used. There are no new-node sources to review.

Step 1 opens every cited statement. `def-pc-integral-scheme` gives nonempty irreducible fibres; `lem-sc-scheme-sober` gives the unique generic point. `lem-sc-integral-function-field-affine-fraction` states that the generic stalk of any integral scheme is a field, so it applies to the fibre itself without requiring the base to be integral or Noetherian. `lem-weil-pbc-module-over-field-flat` gives exactly the fibre-stalk flatness. The base-change clause of `lem-weil-pbc-qcqs-morphism-permanence` gives finite presentation of the restricted family. These are the two flatness hypotheses and the presentation hypotheses of `lem-trf-flat-fibre-free-neighbourhood`. Its conclusion is freeness on an actual neighbourhood, not merely stalk freeness. Tensoring that trivialization with the residue field identifies its integer rank with the item's r(u).

Step 2 uses precisely the open-map conclusion of `lem-weil-pbc-flat-lfp-open`, with flatness and local finite presentation both given by the item's morphism hypotheses. The rest is written out: for v in the image, the free neighbourhood meets the integral fibre, hence contains its generic point, and the same standard basis computes the rank. I checked that no continuity or specialization property of a putative generic-point section of f is being assumed.

Step 3 is elementary compactness, fully written. Open level sets are also closed because all other levels are open. A finite subcover of disjoint nonempty level sets includes every one, and each closed level in the quasi-compact U is quasi-compact. No Noetherian hypothesis or bound on the ranks is needed.

Step 4 cites `lem-weil-pbc-affine-morphism-permanence` clause (1), `lem-weil-pbc-flat-morphism-base-change`, `lem-weil-pbc-qcqs-morphism-permanence` clause (3), and `lem-weil-pbc-fibre-of-base-change`. I read all four statements: they apply to arbitrary base change, and the last gives the cartesian fibre identification over the induced residue-field extension. Further extension to L is proved by the fibre-product universal property. Geometric integrality follows from the hypothesis for *every* field extension. No claim is made that ordinary integrality alone survives field extension.

Step 5 takes exactly quasi-coherence, finite type and quasi-compact/quasi-separated transformed base from clause (2) of `lem-trf-module-admissible-blowup-calculus`. Its agreement-over-U conclusion is explicitly present. `lemma-nagata-admissible-blowup-over-open` gives a specified isomorphism of the inverse image of U with U, hence quasi-compactness and the identification of fibres, local rings and modules used here. Finite presentation and free neighbourhoods are carried through this actual isomorphism. I do not use the calculus node's stronger composition assertion or its global-relative-flatness clause. The latter's hypotheses would not hold for the whole module.

Step 6 sets up the induction with the base case and with quasi-compactness of each preserved open and finite type of each transformed module explicitly included. Those are exactly the inputs needed to reapply the same calculus node. Step 4 supplies the family properties at the next stage; the isomorphism on the preserved open supplies the original restricted module, its relative flatness there at generic points, its presentation and its ranks. It is therefore an induction using earlier steps, not a circular citation or an unproved comparison between different centres. The only non-Mathlib off-unit tool, `lemma-nagata-admissible-blowup-over-open`, is declared in `split_report.tool_uses`; the flattening unit has no replacement for this general blowup-over-its-complement fact.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the files and these source places. All citations use statements, not constructions hidden in proofs; every cited id exists, and a dependency traversal found no path from any proof dependency back to this item. There is no new node to relabel a clause, no missing statement-only-node search, and no change to imported fields. `citations.json` contains exact quotations copied from each cited statement. Each non-elementary step is under 2000 characters; no long step hides an independent comparison lemma.

Small cases checked: U empty (empty partition and no ranks to compare), F zero (rank zero and the empty basis), a base with disconnected components and different ranks (distinct clopen levels allowed), a family of zero-dimensional integral fibres (the unique fibre point), zero blowups (the induction base), and blowup of the unit ideal (identity with empty exceptional centre). Nilpotents in the base are allowed throughout. No step assumes normality, reducedness of the base, or global finite presentation of F outside X_U.

## Unfinished work

None in this stage-1 split. Existing unsplit dependencies remain their own items; no claims about completed Lean proofs are made.
