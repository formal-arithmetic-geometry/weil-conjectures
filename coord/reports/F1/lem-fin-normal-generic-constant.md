# Stage-1 report: lem-fin-normal-generic-constant

Files written:

- `dag/nodes/sec-smooth-purity/lem-fin-normal-generic-constant.json` (item, statement split; no new node).
- `citations.json` (verbatim statement excerpts for the proof step).
- `report.md` (this report).

Attachments: none. The source repository has only the sorry-bearing declaration `AlgebraicGeometry.Etale.isIso_unit_constantSheaf_of_isIntegrallyClosed` in `WeilConjectures/ConstructibleSheaf/FinitePushforward.lean:77-85`, so it is not an attachment.

WANTED: none.

## Not duplicates

`lem-fin-normal-generic-constant` vs `lem-weil-pbc-normal-constant-generic`: the existing node gives a stronger canonical-map/unit formulation for an integral normal scheme and also the nonempty-open case; this item is the Noetherian componentwise formulation for the generic inclusion and retains its own proof route.

## Review by F1

I read the item blueprint proof and the source-repository docstring and declaration in `WeilConjectures/ConstructibleSheaf/FinitePushforward.lean`. The declaration is marked `sorry`, and its hypotheses use the same integral/normal generic-point setting in a more general module-valued form, so it cannot close this item. I also read the existing DAG node `lem-weil-pbc-normal-constant-generic` and recorded it as the same-as duplicate, without using its proof to replace this unit's route.

The sole proof step is the imported componentwise argument. Its first citation states that an etale pullback over a Noetherian normal integral scheme is a finite disjoint union of open-and-closed normal integral schemes, exactly the component decomposition used. The openness citation states that flat locally finite-presentation maps remain open after base change, which gives dominance of every nonempty component. The generic-fibre calculation is written out in the step: an integral finite-type etale algebra over the field `K` is a finite separable field, so each component and its generic fibre contribute one connected component. For the section calculation I replaced the imported definition citation with `lem-weil-pbc-constant-sheaf-sections-connected`, whose statement explicitly identifies global sections of a constant sheaf on a connected scheme with the coefficient group. Finally, the direct-image definition states `(u_*F)(W)=F(W\\times_VU)`, which is precisely the evaluation used to identify the restriction map with the asserted natural map.

I checked the hypotheses in the step: Noetherianity is used by the normal-components node; flatness and local finite presentation are the hypotheses of the openness node; each component is nonempty before applying dominance; and connectedness is supplied by each normal integral component and its nonempty generic fibre. Small cases (one component and `M=0`) reduce to the identity map on `M`, as required.

Mathlib searches were run for the item with LeanFinder, Loogle, grep, and LeanSearch. LeanFinder returned only generic normalization/function-field declarations, Loogle reported an unknown `constantSheaf` identifier, grep found no matching AlgebraicGeometry declarations, and LeanSearch was unavailable; these results are recorded verbatim in the node.

## What was wrong or corrected

The imported step cited `def-weil-pbc-etale-sheaves` for the nontrivial connected-section calculation, but that definition does not state the needed global-section theorem. I corrected the proof dependency and citation to the existing `lem-weil-pbc-constant-sheaf-sections-connected` node. No new node was created because the remaining finite-field and component observations are the short elementary calculations in the step, and all other required facts already exist in the cited nodes.

## What could not be finished

Nothing remains for the stage-1 split; the required dry run is the next check.

## Second reading by F1

- Statement: checked against Stacks Tag 09Z5 and the definition nodes for schemes, integral/normal schemes, residue fields, constant sheaves, etale abelian sheaves, and direct image; hypotheses and finite-abelian conclusion agree.
- Step 1: checked [lem-fin-etale-normal-components], [lem-weil-pbc-flat-lfp-open], [lem-weil-pbc-constant-sheaf-sections-connected], and [def-weil-pbc-direct-image]; each citation states the fact used, and the finite separable field and component-product observations are elementary. The one-component and zero-group cases give the identity map.
- New nodes: none; there are no new-node B1-B7 obligations. The existing stronger node [lem-weil-pbc-normal-constant-generic] was checked as a same-as formulation and is not used as a proof dependency.
- Changed the statement to introduce all objects and cite their definition nodes, and changed the source to Stacks Tag 09Z5 with its label in etale-cohomology.tex; the proof and citations were otherwise left unchanged.
