# Worker report: lem-weil-pbc-smooth-curve-etale-structure-direct-images

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-smooth-curve-etale-structure-direct-images.json`: existing item retained and marked `split`; no new nodes or Mathlib leaves.
- `citations.json`: 35 verbatim statement quotations, one for every cited node in the six proof steps.
- `report.md`: this report.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, the declaration name in the imported Lean metadata, and the structure-sheaf/direct-image terminology. No declaration with this item's exact statement and no blueprint-tagged, sorry-free declaration was found. The `lean` metadata in the shared DAG is archived review metadata with `existing: false`, not an attachment in the current source checkout.

## WANTED

None.

## What was wrong or incomplete

The item was already a complete imported split with all proof dependencies present, but its status remained `unsplit` in the new-target overlay. I found no missing statement dependency, duplicate, source error, or Mathlib leaf. I preserved the existing six-step 0GKA/03P2 argument, its blueprint ancestry, tool-use declarations, and prior review metadata, and changed only the status in the sandbox copy. No statement was corrected.

## What could not be finished

Nothing remains for this stage-1 split. No Lean file was written and no compiler or build tool was run, as required.

## Review by NW

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `coord/dag-sync.md`, `GOAL.md`, delivery-errors sections B–E, the fixed chapter/unit records, the main-20261015 blueprint ancestor `thm-weil-pbc-direct-image-finiteness-proper`, and the imported item. The item source is Stacks `literature/stacks-project/curves.tex`, Tag 0GKA (smooth-curve specialization), with the étale comparison in `etale-cohomology.tex`, Tag 03P2. The source metadata and the six imported proof steps agree with this route.

Step 1 uses exactly the statements of smooth-flatness, proper finite-presentation permanence and base-change permanence, smooth geometrically reduced fibres, the scheme conventions, and the field global-sections result for proper geometrically reduced geometrically connected schemes. I checked that properness supplies separatedness/quasi-separatedness and that the fibre hypotheses are obtained by base change; no reducedness of the base is assumed.

Step 2 uses the perfect-direct-image/base-change theorem, the flat derived structure-unit theorem, and the perfect degree-zero fibre criterion. Their statements give the perfect complex `Rf_* O_X`, the structural unit and its fibre maps, and the conclusion that `O_S → f_* O_X` is an isomorphism together with the local splitting `O_S[0] ⊕ P`.

Step 3 uses the same perfect base-change theorem, locally-Noetherian-from-locally-finite-type, properness, the dimension definition, cohomology vanishing above Noetherian dimension, and the finite-free residue-model theorem. I checked that each fibre is Noetherian and dimension one, so its structure-sheaf cohomology vanishes above degree one; the residue model then gives a finite-free degree-one local model and hence a finite locally free `E = R^1 f_* O_X`. Rank zero and empty fibres are allowed by the stated local model.

Step 4 uses perfect derived base change, Leray, affine quasi-coherent vanishing, the two base-change-map definitions, derived pullback/direct-image adjunction and composition, module pullback adjunction and its identity/composition law, and the existing functoriality theorem for normalized cohomology pullbacks. I opened every cited node and verified that it states the corresponding canonical map or composition law. The long paragraph is one routine unit/counit calculation: the tower `W → V → S` is written explicitly, the composite adjunction unit is compared with the two successive units, and taking `H^1` and affine sections gives the required compatibility. It does not hide a separate lemma.

Step 5 uses the pullback-natural quasi-coherent/étale cohomology comparison, the higher-direct-image presheaf theorem, proper finite-presentation permanence, and the definition of the associated étale quasi-coherent module. I checked the hypotheses on each affine étale base object (`X_V` is quasi-compact separated) and that the coefficient sheaf and sectionwise universe lift are the same. The comparison is natural in restrictions and linear for base-function multiplication, so it yields the compatible bijections `b_V` and the asserted scalar action.

Step 6 uses the affine-open basis, the small étale-site definition, quasi-coherent étale descent, the locally-bijective sheafification criterion, and the sheaf-of-modules definition. I checked that affine covers refine arbitrary étale objects and overlaps, that the target is a sheaf, and that local bijectivity gives the sheafified isomorphism. The same affine-cover argument proves the degree-zero structural map is bijective; the empty-base and rank-zero cases remain valid.

For every step I read the cited node's current statement and copied that statement verbatim into `citations.json`; all 35 `uses` entries occur in `proof_deps`. I checked the two long-step requirements: step 4 is a single explicit derived-adjunction/cohomology-functoriality calculation, so it has no concealed independent lemma; step 6 is below the 2000-character threshold and is an explicit sheaf-gluing argument. I ran the required Mathlib searches for the item (LeanSearch, two LeanFinder phrasings, two Loogle patterns, and two source greps); they returned only general scheme/smoothness declarations or no hits, so the item is not a Mathlib leaf. Small cases checked include the identity base change, empty base, rank-zero `E`, and a geometric fibre over a field.
