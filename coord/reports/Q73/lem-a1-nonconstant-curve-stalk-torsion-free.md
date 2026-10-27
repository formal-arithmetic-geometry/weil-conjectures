# Stage-1 delivery: lem-a1-nonconstant-curve-stalk-torsion-free

Group Q73, 2026-10-24. Direct delivery; self-review below is the signature required by this brief, with independent maintainer review after delivery.

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-nonconstant-curve-stalk-torsion-free.json`: statement, split into five steps; no full Mathlib match. Statement and statement dependencies unchanged.
- `citations.json`: 13 entries, one per cited node per step, quoting the cited statement verbatim.
- `report.md`: this report.
- `searches.jsonl`: actual responses logged by msearch.py, retained in the sandbox.

New nodes: 0. New Mathlib leaves: 0. The split reuses the existing Mathlib leaves for sobriety, dimension's chain definition, and integral stalks in the function field, as well as the existing dimension comparison.

## Attachments

None. The live `lean/WeilConjectures/` search for the item's id and the `(blueprint: ...)` tag returned no declaration. Concept searches in that tree and the read-only Sheaf tree found no declaration giving every clause with these hypotheses. In particular `lean/Sheaf/AlgebraicGeometry/Curve/NonconstantNormalCurveMapFlat.lean:82` states only flatness of a map of two curves with normal target and has `sorry` at line 88; it cannot attach this item, whose integral source is arbitrary. The normalization-stalk declarations have a different geometric setup. The upstream source search did not reveal an exact declaration either.

## WANTED

None. The needed Stacks TeX and Mathlib sources are present and were read locally. No SGA source is used.

## Findings and changes

The imported node has a correct statement and empty proof. I supplied the dimension-one argument for dominance, explicit construction of the injective generic field map, the germ square for every stalk map, and the domain-cancellation argument for torsion-freeness. The arbitrary integral source is intentional: its dimension, finite type, normality, or a k-scheme structure are never needed. The source Stacks 0CCK specializes to maps of curves, but its dominance and stalk argument works under exactly the present broader hypotheses; 0CC1 itself permits arbitrary integral schemes.

The latest blueprint `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-lem-wft-finite-map/lem-a1-finite-map-curve.proof.md`, third paragraph, proves generic etaleness from the nonzero differential. This node is the automatic-flatness input already extracted through `lem-a1-nonzero-differential-generically-etale` and `lem-a1-nonconstant-normal-curve-map-flat`. I preserved that route, the chapter, the inherited unit, and the existing blueprint from/via metadata. No chapter or unit file is changed; this is not the unit's key statement.

## Searches and reuse

I searched the entire DAG for the item, nonconstant/generic/stalk/domain concepts, 0CC1 and 0CCK, and used `tools/blueprint_refs.py ancestor` and searches for `nonconstant`, `dominant integral`, `stalk function field`, and the item's concept. None is another blueprint statement of this item. The existing `lem-sc-integral-scheme-stalks-in-function-field` states the generic-stalk field, all stalk domain properties, and the precise injective germ maps used here; this avoids creating any new geometry lemma.

The following nearby nodes were inspected and not misapplied: `lem-sfb-curve-nonconstant-generic-criterion` needs an algebraically closed base and smooth target, whereas this item has an arbitrary field and possibly singular target; `lem-sfb-dominant-affine-germ-comparison` assumes dominance and an affine inverse image, neither of which can be assumed at the start here; `lem-trf-dominant-affine-chart-data` assumes locally finite type and locally Noetherian data absent for the source; the punctured-DVR normalization nodes concern a different normalization. I cite none of those nodes.

All four requested msearch tools were run with Q73 and this item; the two LeanFinder formulations, two grep queries, Loogle query and LeanSearch query are recorded exactly from searches.jsonl, appended to the pre-existing search records rather than deleting their history. All services answered successfully. I read Mathlib FunctionField.lean:51-95 and 163-179, AffineScheme.lean:843-851, and ClosedImmersion.lean:246-268. They give ingredients or a converse direction, not the two-point-image theorem. The item is therefore split, not declared a Mathlib leaf.

## Not duplicates

No new node is created, so there are no new/existing same-tag pairs to distinguish. The existing function-field leaf is reused rather than duplicated. No item clause has merely been renamed as a new node.

## Review by Q73

I read Stacks `curves.tex` Tag 0CCK, label lemma-flat, complete proof (lines 92-103), and `morphisms.tex` Tag 0CC1, label lemma-dominant-between-integral, all six clauses and the proof (lines 1408-1449). The former supplies precisely the nonconstant, dominant, injective, torsion-free route. The latter applies to integral schemes without finite-type, normality or dimension hypotheses. I also read `properties.tex` Tag 04MU, label lemma-dimension (lines 1233 onward), for the comparison needed because def-pc-curve uses local-ring dimension. The latest blueprint source and the chapter/unit records were open alongside these. No source error or statement dispute was found.

For Step 1 I opened the statements of def-pc-curve, def-pc-integral-scheme, lem-sc-scheme-sober and lem-pc-scheme-dimension-local-rings. The first two give integral, nonempty and irreducible schemes, the sobriety statement gives existence and uniqueness of the generic points, and the dimension lemma equates the supremum convention with topological dimension. The latter is a generic off-unit tool, declared in split_report.tool_uses; the other off-unit results used below are already Mathlib leaves or definitions. No smoothness, normality, or Noetherian assumption enters this step.

For Step 2 I read def-weil-locally-ringed-space-morphism for continuity, def-sc-generic-point for the closure property, lem-sc-scheme-sober for uniqueness, and def-kun-topological-krull-dimension for chains of irreducible closed sets. The actual short argument is written in the step: if z is nongeneric and w is a different specialization of z, closure(w) is strictly inside closure(z), which is strictly inside Y. The first strictness is exactly uniqueness of generic points, and the second is z different from the generic point of Y. This contradicts dimension one, forces closure(z) to be a singleton, and hence contradicts the two-point-image hypothesis. Dense image follows by containing eta_Y. This is a direct argument from the cited definitions and sobriety, not an invocation of the stronger algebraically closed smooth-curve node.

For Step 3 I read the complete statement of lem-sc-integral-scheme-stalks-in-function-field, in particular clause 2 and its explicit description of rho_x. It says that all stalks are domains, that the generic stalk is a field, and that rho_x is injective. It applies to both X and Y because both are integral; it requires no finiteness. The locally-ringed morphism definition supplies the generic stalk map after Step 2 identifies its target point. The field-map injectivity is proved by multiplying a putative nonzero kernel element by its inverse, so no uncited theorem is used.

For Step 4 I opened def-weil-pbc-module-stalk, which states every stalk element is a germ and specifies the germ maps, and def-weil-locally-ringed-space-morphism, which states the section maps commute with restriction and induce the stalk maps. The function-field leaf specifies that rho sends s_x to s_eta. Thus the two sides of the displayed square both send s_y to the germ at eta_X of the same section f_W^sharp(s), as the step explicitly computes. The generic points belong to W and f^{-1}W by the leaf's nonempty-open assertion and Step 2. Injectivity follows by composing with the already injective alpha rho_y. This square is an elementary computation on representatives, not a hidden comparison lemma. All three cited statements contain exactly what is used, and their verbatim statements are in citations.json.

Step 5 uses only the preceding proved facts: an injective ring map sends a nonzero scalar to a nonzero scalar, and a domain has no zero divisors. It writes out the resulting implication phi(a)b=0 => b=0 and matches the statement's specified scalar action. Its uses list is empty and elementary is true; no flatness theorem, finite generation or PID assumption is invoked.

Against delivery-errors B-E, there are no new statement-only nodes to audit and no false auxiliary statement. All non-elementary facts used are statements of cited existing nodes; every citation was checked for C4 rather than borrowed from a node's proof. The proof dependencies are exactly the union of uses, no new dependency points back to the item, and none of the five steps exceeds 2000 characters. I corrected no mathematical hypothesis or conclusion. The source expansion and citation choices are the repairs to the previously missing proof.

Small cases checked: identity of an integral curve; the generic-point inclusion Spec k(Y) -> Y (excluded because its image has only one point); a constant closed-point map (also excluded); a dominant map to a singular integral curve (the proof still works without normality); a source of dimension greater than one such as a product mapping to its curve factor; and a purely inseparable map such as t -> t^p in characteristic p (no separability is needed). In the torsion assertion b=0 causes no issue and the requirement a != 0 is essential. Removing source integrality would allow zero divisors and break the cancellation argument, so that hypothesis has been retained.

## Unfinished work

None in the stage-1 split. No Lean files were written and no compiler, Lake or build command was run. Server checks and the delivery dry run are run through the required launcher tools, never locally.
