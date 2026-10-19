# Stage-1 split: lem-coef-free-resolution-coproduct-augmentation

## Files written

- `dag/nodes/sec-six-functors/lem-coef-free-resolution-coproduct-augmentation.json`: statement preserved; four proof steps; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim quotations for the two existing cited nodes.

## Attachments

None. The requested declaration tag and the free-category/comonad terminology do not occur in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`; no sorry-free Lean declaration states the item.

## WANTED:

WANTED: W. G. Dwyer and D. M. Kan, *Simplicial localizations of categories*, §§2.4–2.6 and Proposition 2.7(iii), printed pp.270–271, for the free-category comonad, standard resolution, and free-product augmentation comparison. The paper is available at the URL recorded in the node but is not archived in `literature/`; I read the primary PDF online and did not download it.

## What was checked and corrected

The item statement in the authoritative shared DAG was copied byte-for-byte. Whole-DAG and whole-blueprint searches found no duplicate support statement; the nearby `lem-coef-dk-cofibrant-localization-comparison` is about hammock localization with a discrete factor and does not state this augmentation. The Mathlib search log contains the required LeanFinder, Loogle, grep, and LeanSearch queries; their hits concern abstract comonads, simplicial augmentations, or model-category resolutions and do not state this mappingwise free-category result. No project Lean attachment exists.

## Review by Q55

I read Dwyer–Kan §§1.4 and 2.4–2.7 in the primary PDF and checked the item against the definitions in `def-nagata-category`, `def-weil-pbc-simplicial-set`, `lem-coef-extra-degeneracy-contraction`, and `lem-coef-kan-quillen-right-proper`. Step 1 checks the free-category functor, counit, comultiplication, and the displayed face/degeneracy formulas directly on generators and words, so the simplicial identities do not assume freeness or cofibrancy of the input categories. Step 2 uses the existing extra-degeneracy statement exactly for the map that composes nested free words; I verified the identity, endpoint, face, and degeneracy equations on generators and the identity-word case. Step 3 follows the proof of Dwyer–Kan Proposition 2.7(iii): reduced alternating words in the coproduct are filtered by their $A$-letters, the outer-bracket contraction is applied to each complete reduced word before the canonical reduction, and the comonad identities handle words whose $C$-part augments to an identity. This avoids the incorrect claim that one may wrap each free block independently as an extra degeneracy. The Kan–Quillen node supplies the stated meaning of weak homotopy equivalence. Step 4 checks empty and singleton object sets, identity-only factors, and arbitrary non-free/non-cofibrant $A,C$; the conclusion is mappingwise for every $x,y$, exactly as required. I created no support node because the only possible smaller candidate would restate the item's Proposition 2.7(iii) clause; the existing generic contraction node is sufficient. No Lean, Lake, compiler, or build tool was run.

## What remains

The paper's short phrase “the argument of the proof of 2.6 also yields” is expanded in Step 3 as the reduced-word filtration and global reduction argument; a second reader should verify that this is the intended Dwyer–Kan construction.

## Second reading by Q55

I read the primary Dwyer–Kan PDF, Section 1.4(iii),(v) on printed p.269, Sections 2.4–2.6 on printed p.270, and the proof of Proposition 2.7(iii) on printed p.271. The item has the same small fixed object set, identity-on-objects functors, free generators for nonidentity arrows, and mappingwise augmentation as those passages, specialized to ordinary constant A and C. There is no missing freeness/cofibrancy hypothesis and no statement correction. The first worker's statement remains byte-for-byte unchanged. The previous review's claim that an outer-bracket contraction descends to reduced coproduct words is superseded by the repair below.

- Step 1: checked against Dwyer–Kan 2.4–2.5 and the explicit definitions in the statement; functorial deletion of identity images, counit/comultiplication identities and the resulting simplicial identities are correct, including empty words; retained.
- Step 2: checked against Dwyer–Kan 2.6, the full equations in `lem-coef-extra-degeneracy-contraction`, and `lem-coef-simplicial-realization-cylinder`; wrote the graph-map naturality identities explicitly and added the cylinder citation to justify realization of the simplicial homotopy; valid even when a nonidentity arrow maps to an identity.
- Step 3: checked against Dwyer–Kan 1.4(iii) and the defining coproduct word relations; wrote the terminating reduction and overlapping-move/induction proof of unique normal forms; elementary and valid for categories with inverses.
- Step 4: checked against the normal forms of Step 3 and the omitted details in Dwyer–Kan 2.7(iii); defined the actual total-length filtration, tuple spaces, identity boundaries, and their degreewise pushout, and checked simplicial stability and augmentation compatibility; elementary construction, including identities created by faces and augmentation.
- Step 5: checked against the full statement of `lem-coef-extra-degeneracy-contraction` and the cylinder homeomorphism in `lem-coef-simplicial-realization-cylinder`; coordinatewise extra degeneracies satisfy every equation on the tuple spaces and their union of identity axes; they are not asserted to descend to reduced words; both comparison maps are weak equivalences.
- Step 6: checked both clauses of `lem-coef-sset-gluing-filtered-equivalences`; both boundary inclusions are degreewise monomorphisms, all three comparisons in each span are weak equivalences by Step 5 and induction, and the indexing poset is the nonempty directed set of natural numbers; gluing and its filtered-colimit clause give exactly the asserted mappingwise equivalence.
- New nodes: none. B1–B7 therefore introduce no new obligations or duplicate statements; the existing Mathlib contraction leaf and existing cylinder/gluing nodes suffice. Direct dependency traversal found no path from any of the three proof dependencies back to the item; all have the item's unit.

Small cases checked: empty O is vacuous; W_0 is a point exactly for equal endpoints and otherwise empty; if A is identity-only, the construction reduces to the ordinary mapping-set resolution; if C is identity-only, the augmentation is the identity on A; empty mapping spaces and zero C slots give empty or constant tuple spaces as specified. Degree zero uses the explicit augmentation section, and degree one uses the stated d_1 identity. Singleton O with A and C both the cyclic group of order two tests cancellations on both sides of an identity C block, the case the original proof did not handle.

Changes and reasons:

1. Replaced the original Step 3 (and its dependent final step) by normal forms, explicit pushouts, contractions on attaching spaces and boundaries, and induction/filtered colimits. The old claim that a global outer bracket exists in the coproduct has no definition. Wrapping C blocks independently fails a required face identity: with A=<a | a^2=1>, C=<c | c^2=1>, in degree one take U=W=[[c]], V=[[c][c]] and the reduced word U a V a W. Its last face deletes V and cancels the two a letters, leaving [c][c]. Wrapping after this face gives the single generator [[c][c]], whereas wrapping blocks first and taking the shifted last face leaves the two-letter word [[c]][[c]]. These differ in F^2 C. The repaired proof uses contractions before attaching and gluing, so needs no compatibility of a contraction with this reduction.
2. Made the correct Proposition 2.6 contraction precise and added the existing realization-cylinder dependency; a simplicial homotopy alone was not the quoted Kan–Quillen node's conclusion.
3. Replaced inherited search records from the earlier ancestor split by actual sandbox searches, including my broader simplicial-monoid/category query, valid ExtraDegeneracy Loogle query, and Mathlib free-product grep. Results were read: abstract cofibrant replacements/Dold–Kan formulas and linear-algebra free products do not state the item; the ExtraDegeneracy results are already represented by the existing cited leaf. The first worker's actual LeanSearch result is retained. No declaration was invented from a failed Loogle query.
4. Regenerated citations.json from the complete verbatim statements of every cited node, with repaired step numbers. No new support node was created. The earlier whole-DAG/whole-blueprint searches and the present direct reading of the nearby fixed-object calculus show that citing that parent would be circular. Read the current main-20261015 ancestor proof, paragraph 2 (derived coefficient adjunction), and retained the existing blueprint ancestry and route.

Read the category definition at Stacks `categories.tex`, Tag 0014, label `definition-category`, and the pinned Mathlib `AlgebraicTopology/ExtraDegeneracy.lean` lines 72–83 and 122–224. Searched both read-only source trees for the item's id and free-category/cotriple names: no attachment states this item. No Lean, compiler, Lake, build, local preflight/check_dag/review_split, live-project write, launcher write, or agent was used. The mandatory delivery command below performs checks on the server.

Required server dry run: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q55 lem-coef-free-resolution-coproduct-augmentation --no-push .` printed `OK (not pushed)` at `7d6924b687`, preflight passed. No failures required further repair. Final delivery is run after recording this result.
