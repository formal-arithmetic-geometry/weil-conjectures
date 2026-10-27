# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-split-node-algebraization-finite-type.json`: statement, split using existing nodes; not a Mathlib leaf. Its statement and statement dependencies are unchanged.
- `citations.json`: twelve step/node entries, each quoting the cited statement verbatim.
- `report.md`: this report. No new nodes or new Mathlib leaves.

The local `prepare.py` is only a sandbox JSON-writing helper; `searches.jsonl` is the search command's log. Neither is a project source file.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for nodal, split-node and Artin-approximation terminology. The few nodal hits concern duality counterexamples, normality or projection formulas; no declaration states this chart theorem. There is no completed Lean proof to attach.

## WANTED

None. All mathematical inputs used here are available in the local Stacks sources.

## Corrections and source comparison

The item was unsplit with no proof. No statement correction or dispute is needed. The given residue-field equality is induced by the morphism, as required for the rational split-node interpretation, and it implies closedness in the fibre by the existing finite-residue-point node. I used the polynomial-model equivalence explicitly present in the statement of `lem-trf-formal-local-structure-nodal-family`, rather than taking that identification from its proof.

The source is Stacks `curves.tex`, Tag 0CBY, `lemma-etale-local-structure-nodal-family`, first proof, third paragraph. Its argument first invokes 0CBX and then 0GDX. Here both supporting statements already exist, so no new node is warranted. The item has the stronger rational split-node hypotheses already in force, so it needs neither residue-field enlargement nor the parent's noetherian-approximation stage. The typo `Z[u,v,t]/(uv-a)` in the source's displayed Y_sigma is read using its declared universal family `Z[u,v,a]/(uv-a)`; the item's family already has the correct variable a.

I read the current main-20261015 locality proof and the unit/chapter records. The current locality proof is the contracting-correspondence argument, while this item's `blueprint.from` records historical nearby-duality/nodal ancestry. I retained that provenance without claiming that the current proof contains the old nodal argument; I changed neither the chapter nor the unit nor the ancestor's route. Blueprint searches for `split node` and `relative approximation` found no blueprint statement equivalent to the item, so `same_as` stays empty.

## Unfinished work

None for this stage-1 split. Existing dependency nodes retain their own statuses; they have not been restated or modified. No Lean was written and no compiler, Lake or build command was run.

## Not duplicates

No new nodes. The existing nodes `lem-trf-formal-local-structure-nodal-family`, `lem-trf-relative-completion-etale-approximation`, and `lem-trf-finite-residue-point-closed-in-fibre` supply the substantive inputs. I searched the DAG by 0CBX, 0CBY, 0GDX and the nodal/relative-approximation keywords before choosing them. The parent `lem-trf-nodal-family-etale-local-model` depends on the item and is not cited back.

## Review by NK

I checked delivery-errors B through E against the item and the local source, including every non-elementary use and every hypothesis in the two main applications. No node is created, so there is no statement-only lemma concealing the item or a clause of it. The proof is an assembly from pre-existing statements with the parameter map and tensor-algebra maps written explicitly. Every step is shorter than 2000 characters.

For step 1 I read the definitions `def-sbc-locally-finite-presentation` and `def-weil-finite-type-morphism`: a finite presentation has finitely many algebra generators. I read `lem-weil-pbc-finite-type-over-noetherian`, whose final clause explicitly covers finite-type integer schemes, and Stacks 01T6, `lemma-finite-type-noetherian`. I read `lem-weil-pbc-affine-open-stalk-localization`, specifically its localization conclusion (c), and `lem-weil-pbc-localization-noetherian`, which states exactly permanence under that localization (Stacks 00FN). This proves the Noetherian hypothesis on A without silently assuming it. Finally, `lem-trf-finite-residue-point-closed-in-fibre` states exactly the needed closedness for a locally finite-type morphism and finite residue extension; our extension has dimension one. Thus no closedness assumption on b in B is used.

For step 2 I read Tag 0CBX, `lemma-formal-local-structure-nodal-family`, and the whole statement of its DAG node. The morphism is flat at z by the item's flatness, locally finite type by step 1, and the base stalk is Noetherian by step 1. Closedness in the fibre, the induced residue-field isomorphism and the completed fibre equation give all three of the node's explicit split-node requirements. Importantly its statement includes the equivalently phrased polynomial model, its marked point o, and the isomorphism as algebras over the completed base. No appeal to an unexported construction or mere abstract ring isomorphism is made.

For step 3 I read `lem-weil-pbc-local-completion-local-ring` and the supporting Stacks 05GI/05GG passages: its statement supplies both the maximal ideal and the unit criterion. Defining t as the inverse-image prime under a maps-to-H ensures the localization map is local, even if b or t is not a closed point of the original integer scheme. I read `lem-weil-pbc-fibre-product-affine-spectra` and Stacks 01I4, `lemma-fibre-product-affine-schemes`, whose tensor description identifies Y_sigma with the actual M_H from step 2. The explicit generator maps preserve the completed-base scalars and the point over the closed completed-base point.

For step 4 I read the full statement of `lem-trf-relative-completion-etale-approximation` and Tag 0GDX, `lemma-relative-map-approximation-pre`. The DAG version assumes both bases finite type over the integers, which B satisfies by hypothesis and T by construction; its locally-finite-type hypotheses hold by step 1 and the two-generator presentation of Y/T. Step 3 gives the local sigma, the required point and the algebra-compatible completed isomorphism. The cited node's conclusion explicitly includes both etale maps, an etale V-morphism to the base change, the commuting diagram, the marked points and both required residue isomorphisms. This conclusion gives every geometric clause of the item without demanding that approximation recover the entire original formal isomorphism.

For step 5 I again read the affine fibre-product statement, plus `lem-weil-pbc-affine-morphism-relative-spec` parts (2) and (4), and Stacks constructions 01LW/01LX. These give precisely the affine chart and restriction statements used. The displayed algebra maps evaluate a to the restricted h, fix the coefficients and u,v, and are inverse by checking those generators; they therefore commute with restriction. Consequently the local identifications glue canonically to the required relative spectrum, with its structural projection. The two generic off-unit tools (stalk localization and relative spectrum) are declared in `split_report.tool_uses`; the other off-unit inputs are Mathlib leaves or definitions.

I tested the small cases h=0 (the split crossing), a field base (where the parameter in its maximal ideal is zero), positive and zero residue characteristic, nonclosed base points, and a nonreduced finite-type base. None of the steps assumes a domain, regularity of the base, invertibility of 2, smoothness away from the node, or global nodality of the family. The item marks a point, so an empty source cannot satisfy its hypotheses. Residue-field preservation is supplied by elementary etale approximation, not asserted for an arbitrary etale neighbourhood.

The four search modes and a second LeanFinder formulation ran through msearch.py with their exact queries and returned results recorded. The hits concern standard smooth presentations, formally smooth algebras and the etale locus, which do not state either nodal completion or relative algebraization. I kept the imported historical searches and added only the five searches actually run in this sandbox. All twelve citations in citations.json are literal text from the cited statements, not their proofs. I checked that the cited statements' dependency closures do not include the item, using the server DAG check as final verification.
