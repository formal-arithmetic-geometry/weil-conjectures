# Stage-1 report: lem-sfb-composition-finite-affine-twist-bounds

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-composition-finite-affine-twist-bounds.json: existing statement, now split into four proof steps; no Mathlib match for the complete item.
- citations.json: seven verbatim statement excerpts, one for every step/node citation.
- searches.jsonl: results recorded by the required msearch.py command; the item's inherited search records were retained.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves reused: lem-sfb-finite-type-composition-base-change, def-weil-finite-type-morphism, and lem-weil-pbc-qcqs-finite-affine-open-cover.

## Attachments

None. I searched the current project under lean/WeilConjectures by the exact blueprint id and by relative ampleness, absolute twists, tensor ampleness and finite affine covers. No declaration gives all the item's clauses. The nearby projective-graph twist result concerns relative Serre vanishing over Noetherian schemes, not this assertion.

## WANTED

None. The sources needed are present locally.

## Corrections and scope

The imported item had no proof. Its statement, statement dependencies and inherited blueprint metadata are retained. Its finite type and quasi-compactness assumptions are sufficient without extra separatedness or Noetherian hypotheses. The earlier Mathlib searches have been retained and fresh logged LeanFinder (two phrasings), Loogle, LeanSearch and grep searches were added. Their hits concern affine-cover constructions or module tensor/pullback, not the eventual ampleness assertion.

The existing blueprint.from.node is null. The required ancestor command likewise reports None; this inherited metadata is not changed. The existing attribution identifies the finite-cover reduction of 0C4K used in the alteration modification-tower argument. This item is not the unit's key theorem, so no unit record is changed.

## Not duplicates

No new nodes were created. I searched the whole DAG by tags 0892, 01T3, 01T4 and by ample twists and finite affine covers, and ran blueprint_refs.py searches for ample, 0892 and finite affine cover. The reusable 0892(1) node lem-sfb-relative-ample-absolute-twist already exists in the same unit and is used directly. Finite-type permanence and finite affine covers are already Mathlib leaves, so neither was recreated. No imported blueprint statement found in the searches states the complete item.

## Review by NN

I read Stacks morphisms.tex at lemma-ample-composition (Tag 0C4K), its proof's finite affine-cover reduction, lemma-pullback-ample-tensor-relatively-ample (0892), definition-relatively-ample (01VH), and the composition/base-change finite-type lemmas (01T3 and 01T4). There are no new-node sources to review. The proof follows 0C4K only through its local bound construction; it does not cite the stronger composition conclusion as a black box.

Step 1 uses clause (1) of lem-sfb-finite-type-composition-base-change for h, the exact finite-type definition for quasi-compactness, and lem-weil-pbc-qcqs-finite-affine-open-cover for the finite family. I opened each statement: the cover lemma requires only quasi-compactness, despite its id containing qcqs, and the permanence lemma requires no separation. I also read the Mathlib composition instances and finite affine-cover theorem in Morphisms/FiniteType.lean and Morphisms/QuasiCompact.lean.

Step 2 uses clause (2) of that same permanence node. The restriction is explicitly identified with the base change along the target open by the universal property of an open subscheme. This does not restrict the source arbitrarily, so no unsupported claim that arbitrary open restrictions preserve quasi-compactness is made. The second citation to the finite-type definition supplies quasi-compactness of f_i.

Step 3 is elementary from the definition in def-sc-invertible-module: restrict the rank-one trivializations. For ampleness I checked the hypotheses themselves: V_i is affine in S, and an affine W open in the open Y_i is affine open in Y. The two inverse-image opens coincide, and iterated restriction is the same sheaf restriction. Thus no theorem about preservation of absolute ampleness under an arbitrary open immersion is smuggled into this step.

Step 4 uses only the statement of lem-sfb-relative-ample-absolute-twist. I read it in full: its hypotheses are precisely quasi-compactness of f_i, invertibility of both modules, ampleness above every affine open of Y_i, and absolute ampleness of M_i. The preceding steps verify each. Its conclusion provides every exponent beyond a nonnegative bound, not merely some sufficiently divisible exponents; this distinction is also explicit in the last paragraph of the proof of 0892(1). Bounds are chosen separately for the finite index set; no global maximum or restriction/tensor comparison theorem is needed for the claimed local conclusion.

For the small cases, S empty admits r=0; maps to the empty scheme force X and Y empty, and no bound must be chosen. If some inverse-image X_i or Y_i is empty, local trivializations and the ampleness conditions are vacuous on that scheme and 0892(1) still applies. Exponent zero is permitted only when it lies beyond the chosen bound, using the structure-module convention already in the item. No assertion forces a zero threshold when M is trivial; 0892 supplies the appropriate bound. The identity-morphism case reduces to the existing absolute ample-twist lemma as expected.

I checked delivery-errors B--E: no statement-only node has a hidden proof because there are no new nodes; the cited statements supply exactly the claims taken from them; finite-type and ampleness hypotheses are checked at the correct schemes; no cyclic dependence on the parent composition lemma is introduced. Every step is under 2000 characters, and the entire assembly proof is under 3000 characters. I generated each citations.json quote from the opened statement and verified it is a literal substring. There was no mathematical statement correction and no route departure. Definitions and Mathlib leaves used from other units are allowed generic tools; the substantive twist lemma is in this item's own unit.

## Unfinished work

None in the requested one-level split. The existing eventual absolute-twist lemma remains its own independently split dependency.
