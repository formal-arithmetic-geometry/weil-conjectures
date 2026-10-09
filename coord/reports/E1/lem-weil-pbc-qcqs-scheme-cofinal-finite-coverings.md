# Delivery report: lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings.json`: statement node, split; no new nodes; Mathlib verdict remains no exact match for the complete refinement statement.

## Attachments

- `pqf-lem-qs-intersection-qc` is used as an existing public node for quasi-compact intersections of quasi-compact opens in a quasi-separated scheme.

## WANTED

None. The cited Stacks source is available in `literature/stacks-project` on the worker checkout used for verification.

## What was wrong or incomplete

The imported node had an empty proof despite its source giving the ingredients. It is now split into: (1) affine basis refinement followed by a finite subcover from quasi-compactness, and (2) quasi-compactness of pairwise intersections using the existing `pqf-lem-qs-intersection-qc` node. The latter is outside unit `sk-thm-p1`, so it is explicitly recorded under `tool_uses` as a generic scheme-topology tool, as permitted by the Stage 1 contract.

Mathlib searches were refreshed conceptually for the complete statement. Mathlib has the ingredients `AlgebraicGeometry.Scheme.isBasis_affineOpens`, `IsCompact.elim_finite_subcover`, `AlgebraicGeometry.IsAffineOpen.isCompact`, and `quasiSeparatedSpace_iff_forall_affineOpens`, but no declaration asserting the full cofinal refinement statement.

## Could not finish

Nothing remains for this Stage 1 item. The global DAG checker still reports unrelated unreachable nodes; the item-specific review passes.

## Review by E1

I checked the two proof steps against Stacks 01IT, 01KO, and 00E8 and against the node's `sk-thm-p1` route. The finite affine refinement uses the affine basis and quasi-compact finite-subcover argument; the pairwise-intersection step correctly invokes the existing public `pqf-lem-qs-intersection-qc` as a generic tool and records that use explicitly. The Mathlib declarations cited are ingredient matches, while the complete cofinality statement remains correctly unsplit. The worker reports passing item-level checks and no new private lemma; I accept the delivery.

