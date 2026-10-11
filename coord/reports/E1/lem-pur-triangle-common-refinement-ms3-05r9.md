# Stage 1 report

Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-triangle-common-refinement-ms3-05r9.json`: statement split, no new node; Mathlib searches found only generic triangle-completion APIs.
- `citations.json`: verbatim citations for every proof-step dependency.
- `report.md`.

Attachments: none.

WANTED: the checkout does not contain the full proof text for Stacks Derived Categories Tag 05R9. I read the published Tag 05R9 page at `https://stacks.math.columbia.edu/tag/05R9`; it states the filtered outgoing-denominator version. This item is the incoming-denominator dual, so the proof below dualizes the source construction using the second halves of MS2 and MS3.

No new node was created. The two constructions are the two clauses of this item itself, so making either one a child node would merely restate a clause (delivery-errors D1). The existing triangle-completion node is strictly smaller and supplies the needed completion fact.

## Review by E1

I read the published proof of Derived Categories Tag 05R9 and the statements of `def-pur-saturated-triangulated-localization` and `lem-pur-triangle-completion-ms6-05r9`. The item introduces the incoming category of triangle denominators and asks for finite common predecessors and equalization of parallel arrows. The definition node explicitly supplies MS1 (identities and composition), MS2 (common denominator squares), MS3 (both equalization directions), and cofilteredness of S/X; the completion node explicitly supplies a distinguished triangle and all three S-components extending a denominator at one vertex. The source has outgoing arrows, so I checked the incoming proof as its dual rather than silently treating the published statement as identical.

Step 1 uses cofilteredness of S/X from the definition and the completion node's extension statement, then rotates to Y and Z. For the resulting component maps I checked the f-square explicitly: their two paths agree after postcomposition with the Y-denominator into the target triangle, so the second MS3 clause permits a further precomposition; the same calculation applies after rotation to g and h. Binary refinements give a finite-family refinement, including the identity triangle for the empty family. Step 2 uses the second MS3 clause and the completion statement: the parallel X-components agree after postcomposition with the target denominator, then a completed precomposition equalizes them; rotation repeats for Y and Z. Step 3 only identifies the two cofilteredness conditions. The hypotheses on distinguished triangles and S are the same as in the item and in the cited completion statement.

I ran LeanFinder, Loogle, grep, and LeanSearch through `msearch.py` for the item. LeanFinder returned generic `complete_distinguished_triangle_morphism` declarations only; grep found no matching common-refinement theorem; Loogle and LeanSearch were unavailable for this query. I tested the finite-family induction at the singleton and pair cases and the equalization procedure at one component before extending it componentwise. No duplicate or closed Lean declaration was found.

## Second reading by E1

- Item statement: checked against the incoming (cofiltered) dual of Stacks Tag 05R9 (`lemma-limit-triangles`) and the existing incoming triangle-category node; hypotheses on the pre-triangulated category, saturated compatible system, fixed distinguished triangle, and componentwise $S$-maps are present; verdict: consistent.
- Step 1: checked each use against the MS2/MS3 clauses of `def-pur-saturated-triangulated-localization` and the three-vertex extension in `lem-pur-triangle-completion-ms6-05r9`; the $f$-square calculation is written explicitly and rotations preserve prior equalities; verdict: valid after incoming dualization.
- Step 2: checked the equalization direction against the second MS3 clause and completion lemma, with successive precomposition preserving earlier component equalities; verdict: valid.
- Step 3: checked that the resulting maps are objects/arrows of the stated triangle category and that MS1 handles the empty family and composites; verdict: elementary and valid.
- Existing dependencies: opened both cited node statements and verified that neither is used through proof material not present in its statement; verdict: citations sufficient.
- Mathlib search record: replayed the recorded LeanFinder/Loogle/grep/LeanSearch queries; no exact common-refinement/equalization declaration, with Loogle and LeanSearch unavailable as recorded; verdict: no Mathlib leaf.
- Edge cases: singleton and empty finite families reduce to the given object and identity triangle; one-component equalization is exactly MS3; verdict: no vacuity or direction error found.
- Metadata: repaired `created.item` to the delivered item so ownership matches the split.

No new node was created: both clauses are the item’s proof obligations rather than independent facts, and the existing completion node is the only strict helper.
