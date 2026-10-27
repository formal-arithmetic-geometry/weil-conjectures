# Worker report: lem-sfb-noetherian-dvr-properness

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-dvr-properness.json`: statement, split; the original statement is unchanged. Eight proof steps establish both directions of the DVR test.
- `dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-image-boundary-dvr.json`: statement, unsplit; a finite-type image's missing boundary point can be reached by a DVR square. Mathlib searches found no match. This is the only new node; there are no new Mathlib leaves.
- `citations.json`: a verbatim statement quote for every node used by every proof step.

The sandbox initially contained only dispatcher marker files. I copied the live item, retained its earlier searches and provenance, and added the split. The newly run searches and actual service results are recorded in `searches.jsonl`. No Lean, compiler, Lake, or repository write was used.

## Attachments

None. Searching `lean/WeilConjectures/` for the item id, Noetherian valuative criteria, DVR properness, and related declaration names found no declaration proving the item. The project occurrences of `IsSeparated.valuativeCriterion` use Mathlib's full criterion; they do not implement the Noetherian DVR reduction. The pinned Mathlib's `AlgebraicGeometry/ValuativeCriterion.lean:29` explicitly lists that reduction as future work. At line 341, `IsProper.of_valuativeCriterion` assumes the condition for every valuation ring. It is not a one-line specialization of the DVR assumption.

## Literature

WANTED: none.

For the item I read Stacks `limits.tex`, Tag 0208 (`lemma-Noetherian-dvr-valuative-proper`), including the entire proof and diagram `equation-solid`. I also read the finite-type diagonal portion of Tag 0207 (`lemma-Noetherian-dvr-valuative-separation`), Tag 0CM2 (`lemma-reach-point-closure-Noetherian`) and its proof. The split follows the Chow proof of 0208. The boundary-point lemma packages the common DVR input for the diagonal argument and the Chow argument; it is a result about arbitrary finite-type images, not a properness criterion or a clause of this item.

For the new node I read Tag 0CM2 in `limits.tex` and its cited algebraic DVR existence lemma in `algebra.tex` (`lemma-exists-dvr`, lines 29312 onward). The latter explicitly requires a local Noetherian domain that is not a field. This is why the new node is restricted to points outside the image. Its statement does not impose a generic-function-field identification, which this item's all-DVR hypothesis never needs. The future worker can follow the source proof with the nontrivial-specialization hypothesis now explicit.

I read the statements of every cited DAG node, including their hypotheses, and the supporting Stacks statements for Chow (0200, `coherent.tex`), immersion closedness (01IQ, `schemes.tex`), the diagonal immersion (01KJ, `schemes.tex`), finite-type composition/base change/Noetherianity (01T3, 01T4, 01T5, 01T6, `morphisms.tex`), locally Noetherian quasi-separatedness (01OY, `properties.tex`), and descent of universal closedness under a surjection (03GN, `morphisms.tex`).

## What was wrong and what changed

The item's statement is correct and has not been weakened. It previously had no proof. Its source gives a stronger criterion testing generic function fields; the present split only needs the all-DVR clause actually stated by the item. Accordingly, Chow's birational refinement and identification of function fields can be omitted while keeping the source's Chow/boundary proof route.

The inherited `blueprint.from.node` is null. `tools/blueprint_refs.py ancestor lem-sfb-noetherian-dvr-properness` also returns None. I retained that lineage and its detailed place/via list; the new node adds this item to the via list. The relevant recorded place is the stable-pointed-Isom properness input below alteration reduction for `det-thm-sf-ctf-stability-direct-images`, clause (3). I read the current main-20261015 direct-images text and the chapter/unit records. No chapter or unit route is changed, and this item is not the unit's key statement. No realization fields were edited.

## Source error

STATEMENT-DISPUTED: the unrestricted statement of Stacks 0CM2, as present in the local source, asks for a DVR of fraction field equal to the residue field of a generic point even when the chosen closure point is already in the image. Take the identity of `Spec(F_p)` and its unique point. The asserted fraction field would be `F_p`, which has no nonfield valuation subring, so there is no such DVR. The proof also invokes `algebra-lemma-exists-dvr` without verifying its explicit nonfield hypothesis in that case.

The new node states only the valid boundary-point case: the chosen point must lie outside the image. Then the image of any generic source point specializing to it is distinct from it. In the source proof, the image of the target local ring in that generic residue field is a Noetherian local domain with nonzero maximal ideal, so the cited DVR-existence theorem applies. This restriction preserves exactly everything the diagonal and Chow boundary arguments use. It changes neither this item's criterion nor any target statement. No invalid unrestricted 0CM2 claim is introduced into the DAG.

## Not duplicates

No existing DAG source carries Tag 0CM2 (searched before creating the new node). Whole-DAG searches by tag, closure/image/DVR terminology, and whole-blueprint searches for valuative criteria, closure of the image, discrete valuation, and boundary did not find this statement.

lem-sfb-noetherian-image-boundary-dvr vs lem-sbc-noetherian-specialization-trait: the latter realizes a prescribed specialization in one scheme, without a prescribed generic lift through a finite-type morphism; the new node supplies a compatible square and fraction field needed for that lift.

lem-sfb-noetherian-image-boundary-dvr vs lem-sc-picard-closure-specialization: the latter finds an image point specializing to a closure point for a quasi-compact map, but constructs no DVR or compatible scheme square.

lem-sfb-noetherian-image-boundary-dvr vs lem-sfb-generic-dvr-properness-criterion: the latter is a properness criterion for an integral separated source, not a DVR realization for a boundary point of an arbitrary finite-type morphism. It is not used to repackage the current item.

lem-sfb-noetherian-image-boundary-dvr vs lem-sfb-noetherian-dvr-properness: the new node has no properness conclusion, uniqueness condition, or extension conclusion. It produces a solid square reaching a boundary point; the item's steps supply the separate diagonal and Chow contradictions.

## Mathlib searches

For both the item and the new node I ran the required `msearch.py` commands for LeanFinder, Loogle, source grep, and LeanSearch, and a second semantic phrasing. All services answered. Queries are copied exactly into the node records. Item hits concerned the all-valuation-ring criterion; the new-node hits concerned generic valuative-square structures, an already assumed valuative criterion's specialization consequence, projective spectra's existence theorem, or `Scheme.range_fromSpecStalk`. None constructs the required DVR through an arbitrary missing finite-type image point. I read the relevant valuative definitions and theorem statements in the pinned Mathlib source. Grep returned no DVR curve-selection result. The new node therefore stays statement-only and unsplit.

## Review by O3

I checked the actual source and cited statements, not only the dependency lists. The item is precisely the equivalence of clauses (1) and (3) in 0208, and the proof retains finite type over a locally Noetherian base throughout. The source error above concerns only a helper's overbroad assertion, repaired in the new helper before use.

Step 1 uses `def-weil-proper-morphism` for separatedness, `def-sc-discrete-valuation-ring` for its valuation-ring characterization, and `lemma-nagata-proper-separated-valuation-extension` for existence and uniqueness. The latter explicitly gives both for proper separated maps, so no converse criterion is smuggled into this step.

Step 2 uses `pqf-def-locnoeth` to choose the Noetherian affine cover, `lem-sfb-finite-type-composition-base-change` for finite type of the restrictions, and the exact universal property in `def-pc-fibre-product` to transfer both existence and uniqueness. `lemma-nagata-projective-target-local` states properness descent from an open cover of the target; `lem-weil-pbc-finite-type-over-noetherian` then supplies a Noetherian and quasi-compact source after this reduction. This avoids assuming the original base is quasi-compact.

Step 3 uses finite-type base change and composition for the relative product T, and finite-type-over-Noetherian for its Noetherianity. `lem-weil-pbc-locally-noetherian-quasi-separated` really states quasi-separatedness of the scheme T. `lem-weil-pbc-diagonal-immersion` supplies precisely the relative diagonal immersion; `lem-weil-pbc-immersion-base-change-lft` supplies locally finite type, not finite type. I explicitly obtained the missing quasi-compactness from `lem-weil-pbc-qcqs-morphism-permanence` using the quasi-compact source and quasi-separated target, and then used the definition of finite type.

Step 4 applies the new helper to that finite-type diagonal and its Noetherian target. The two projections of the trait map lie over the same map to S and have identical generic restrictions, so the item's uniqueness applies. The fibre-product statement explicitly makes their pair the diagonal of their common value, giving a contradiction at the closed point. `lem-weil-pbc-immersion-closed-image-closed-immersion` and the definition of separatedness then give separatedness of f. Nothing about an arbitrary pair of points of a fibre product is inferred from equality of underlying points.

Step 5 applies `lem-weil-pbc-chow-noetherian` only after S is Noetherian and f is separated. Its statement provides the proper surjection and the immersion into projective space with the required equality of composites. The projective-space node explicitly states properness over every base. The definition of proper and finite-type composition show X' and projective space have finite type over S; the existing Noetherianity lemma then applies to both.

Step 6 again checks both halves of finite type for the immersion, citing the same actual quasi-compactness and locally finite type statements as step 3. Thus the new boundary lemma applies with target P; the chosen y is outside the image, exactly its additional hypothesis. This does not require normality, reducedness, excellence, or a residue-field equality.

Step 7 checks the two commutative squares by their equations. First the item's existence lifts the square for f; then the proper-valuative-extension node lifts the square for pi. The separated-valuation-uniqueness node is used only for q, which is proper and hence separated. The equalities of generic restrictions and composites to S are written explicitly before using uniqueness. This is the contradiction that closes the Chow immersion's image.

Step 8 uses the actual closed-image-immersion equivalence, closed-immersion/proper composition statement, and `lem-weil-pbc-image-universally-closed`. The last node explicitly allows an arbitrary surjective map from a universally closed S-scheme and explicitly concludes properness when the target morphism is separated and locally of finite type. Its hypotheses have all been established; this is not an unsupported cancellation of properness.

I checked empty source/base cases (the criterion and argument are vacuous or immediate there), the nonseparated doubled-origin example (its two DVR lifts violate uniqueness), and a punctured affine line over a field (the missing origin gives the ordinary local DVR and violates existence). For the new node, empty images and closed immersions have no boundary points, while `D(t)` in `Spec(k[t])` at the missing origin is witnessed by `k[t]_(t)`. Non-Noetherian bases are not asserted, and no excellent-DVR assumption is added. I also checked the finite-field counterexample to the unrestricted source lemma. All eight proof steps are below 2000 characters; none hides a separate comparison lemma. The new node has no proof or proof dependencies; it is not an elementary step, a clause of this item, a duplicate, or an unrecorded Mathlib leaf.

The only explicitly declared off-unit tool is Chow domination; it is a generic geometric input and replaces no step of the unit's constructibility route. All other reused off-unit lemmas are Mathlib leaves or recorded closed nodes. The citations file was assembled from the cited statement text, preserving the verbatim wording.

## Unfinished work

No part of this one-level split remains unfinished. The new boundary-DVR statement intentionally joins the stage-1 queue unsplit. Delivery and independent mathematical review remain the prescribed next steps.
