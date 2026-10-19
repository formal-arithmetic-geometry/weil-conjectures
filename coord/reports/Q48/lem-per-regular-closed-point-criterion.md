# Q48: lem-per-regular-closed-point-criterion

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-closed-point-criterion.json`: statement, split into four steps, unchanged statement; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-locally-noetherian-closed-specialization.json`: statement-only unsplit lemma, Stacks 02IL, no Mathlib match.
- `citations.json`: verbatim statement excerpts for all seven step/node citations.
- `report.md`: this report. Existing `searches.jsonl` retained and extended only by msearch.py.

One new node; zero new Mathlib leaves. No Lean files, compilation, build or live-project writes.

## Attachments

None. Searched the whole read-only slopmaster2 `WeilConjectures/` by the item id, regular/closed-point terminology and IsRegularLocalRing. Read `WeilConjectures/AlgebraicGeometry/Regular.lean` and `WeilConjectures/Mathlib/AlgebraicGeometry/Noetherian.lean`: neither states the criterion or the general closed-specialization theorem. The regularity class is stalkwise, not a closed-point criterion. Smoothness results at closed points have finite-type/field hypotheses and do not attach. No sorry declaration in the read-only upstream master was treated as a proof.

## WANTED

None. All sources used are present locally.

## Audit and changes

The sandbox initially had only four logged searches, no node or report, so there was no split to dry-run or discard. I retained that search log and read the returned concepts; the inherited item also retains its prior Q42 searches. The exact Q48 queries and actual outputs/digests were appended to the item's Mathlib searches. The new node records only searches actually made for its own closed-specialization assertion, including a second natural-language formulation. Loogle returned zero hits. LeanFinder and LeanSearch returned local-ring closed points, Noetherian scheme definitions and sobriety; the alternative phrasing also returned Jacobson-space theorems, whose hypothesis is unavailable here. Grep returned local-spectrum specializations, affine inverse-limit and etale-point results, not 02IL. Mathlib's Noetherian.lean has no closed-point-existence theorem. `IsLocalRing.specializes_closedPoint` applies to the spectrum of one local ring; it does not provide a globally closed point of an arbitrary scheme. The returned Jacobson-space result was read in `Topology/JacobsonSpace.lean` (lines 82 and 107): locally Noetherian schemes are not necessarily Jacobson.

The statement is correct as imported: no STATEMENT-DISPUTED issue and no change of hypotheses. The important subtlety is that an affine-open closed point need not be closed in X. Properties 02IL is the genuine missing geometric input; it is not an elementary topological compactness argument, because X need not be quasi-compact. I did not create a duplicate of the existing regular-local localization node or a new theorem merely restating the closed-point criterion.

The chapter and unit records were read. This auxiliary lemma lies below the regular-model completion used in the dimension-normalized duality part of `lem-per-artin-gabber-affine-curve`. It is not the key statement of its Fourier unit, so no unit realization was changed. The proof follows Properties 02IT's stated route: closed specialization and localization of a regular local ring. The two off-unit statement tools are declared in `split_report.tool_uses`; both are generic tools, not replacements of a unit argument. Definitions and the existing affine-stalk Mathlib leaf need no route exception.

Blueprint searches: `blueprint_refs.py ancestor lem-per-regular-closed-point-criterion` gives `lem-per-artin-gabber-affine-curve`; searches for `closed point`, `regular local`, `02IL` and `02IT`, and a whole-blueprint search for `02IL`/its source label were used to check provenance and duplicates. No blueprint node supplies the new 02IL statement or the item. The new node has that ancestor, precise supporting place and the item prepended to its via list. Existing blueprint provenance fields are retained.

## Not duplicates

- lem-per-locally-noetherian-closed-specialization vs lem-sc-quasi-compact-kolmogorov-closed-point: the existing statement requires global quasi-compactness; the new one assumes local Noetherianity and allows arbitrary non-quasi-compact schemes. Neither is a one-line specialization of the other under the item's hypotheses.
- lem-per-locally-noetherian-closed-specialization vs lem-per-punctured-local-closed-points: the existing statement is a Jacobson assertion for the punctured spectrum of a Noetherian local ring; it does not give a point closed in an arbitrary locally Noetherian scheme.
- lem-per-locally-noetherian-closed-specialization vs lem-per-regular-model-completion: the latter uses 02IL/02IT in its proof but its statement is about completion of a regular model, not closed specializations. A tag occurrence in a proof is not a duplicate statement.

Whole-DAG searches for 02IL and `locally-Noetherian-closed-point` found no existing node stating this assertion. The whole-DAG statement search also checked closed-point/specialization and localization terminology. The new node has no regularity hypothesis or conclusion and is therefore not a clause of the item.

## Review by Q48

I read Properties `lemma-characterize-regular` (02IT), lines 1141–1161, including all three equivalent assertions and its proof; `lemma-locally-Noetherian-closed-point` (02IL), lines 555–588, including its proof; Algebra `lemma-localization-of-regular-local-is-regular` (0AFS), lines 27126–27140; and Schemes `equation-canonical-morphism` (02NA) and `lemma-specialize-points` (01J7), lines 2370–2421. The tag/label mapping was checked in `literature/stacks-project/tags/tags`. For the new node, 02IL explicitly gives every point a specialization closed in the ambient scheme. Its proof uses the special structure of Noetherian local rings to obtain global closed points, so I kept it as a real unsplit lemma.

Step 1 uses the all-stalks characterization explicitly in the statement of `def-weil-regular-scheme`. It is the (1)–(2) characterization, not the (1)–(3) closed-point criterion under construction. Restricting the universal quantifier is elementary. The same definition statement is used at the end only after all stalks have been proved regular. I checked that this definition node does not depend on this item; this does not create a circular proof.

Step 2 uses the new 02IL node at the arbitrary point x. The local Noetherianity hypothesis is exactly the item's hypothesis. The resulting point c is closed in X itself, so the assumed regularity at closed points applies to A = O_(X,c). Neither quasi-compactness nor Jacobsonness has been added.

Step 3 uses clauses (1) and (2) of `lem-weil-pbc-spec-local-ring-canonical-morphism`: its statement supplies both the image as all generalizations and the isomorphism on every stalk. The relation c in closure{x} has the right orientation, putting x in that image. I opened the node and copied these clauses into citations.json. I also opened `lem-weil-pbc-affine-open-stalk-localization`: its clause (c) identifies the stalk of the entire affine scheme Spec A at q with A_q. `def-weil-affine-spectrum` gives its global sections as A. These statements, rather than their internal proofs, give the claimed composite isomorphism O_(X,x) = A_q. No new stalk-comparison lemma is hidden here.

Step 4 uses precisely the first clause of `lem-weil-pbc-regular-local-localization`, for the regular local ring A and a prime q of A; it does not use the distinct regular-ring localization theorem, which would require the desired regularity already. The isomorphism transports the maximal ideal, finite generating sets, Noetherianity and prime chains, hence regular localness. That is elementary transport of the definition, also supported by Mathlib's `IsRegularLocalRing.of_ringEquiv`. The all-stalks conclusion and given local Noetherianity then give regularity by the definition's explicit characterization.

I checked B1–B10, C1–C8, D1–D5 and E1–E7 against the files and sources: one genuine statement-only new node, self-contained hypotheses, definition references, exact tags, actual logged Mathlib searches, blueprint provenance; every non-elementary input has a cited node whose statement says it; no proof-only object is borrowed; the converse carries its argument rather than relabelling it. No statement was corrected because no false statement was found. There are no steps over 2000 characters (lengths 360, 404, 708, 796), no induction, descent or denominator-clearing argument concealed in a step, and no SGA citation.

Small cases: the empty scheme makes both sides of the criterion and the new universal assertion vacuous; Spec of a field has one closed point and is regular; a regular DVR tests the generic-to-closed specialization and localization A_(0); Spec(k[epsilon]/epsilon^2) is a nonregular one-point scheme, so its sole closed stalk correctly fails the hypothesis. Infinite disjoint unions of Noetherian affine schemes test that the new node and the proof need no global quasi-compactness. On an open affine neighbourhood a point may be closed only in that open, which is why Step 2 specifically uses 02IL. Spec of a DVR is not Jacobson, so the Jacobson-space Mathlib hit cannot replace the new node.

## Unfinished work

No gap remains in the item's natural-language proof. The single new node is intentionally statement-only and unsplit, as required for a one-level stage-1 delivery. The required server dry run exited 0 and printed `OK (not pushed)` at 87b6aa9e6e, with preflight passed. A final dry run is repeated after recording this result, before direct delivery; the final push commit is the commit printed by deliver.py.
