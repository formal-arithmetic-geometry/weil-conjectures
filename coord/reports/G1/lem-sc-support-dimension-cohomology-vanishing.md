# Stage-1 worker report

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-support-dimension-cohomology-vanishing.json` (split statement)
- `dag/nodes/sec-picard-framework/lem-sc-support-factor-closed-pushforward.json` (new unsplit statement node; no Mathlib match)
- `dag/nodes/sec-picard-framework/lem-sc-closed-subset-noetherian-space.json` (new Mathlib leaf: `TopologicalSpace.NoetherianSpace.set`)
- `citations.json`

## Attachments

`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_topologicalKrullDim_lt` in `WeilConjectures/AlgebraicGeometry/Cohomology/EulerChar.lean:64-73` was checked and has `sorry`; it does not state this support-localized item exactly, so it is not attached.

## WANTED

None.

## Review by G1

I read the imported item and its blueprint ancestor `thm-sc-p1-duality`, including the parenthetical Ext-vanishing clause, and checked the Stacks sources `cohomology.tex` Proposition 02UZ and Lemma 02UV and `sheaves.tex` Lemma 00AE. The target's support is a closed subset, so Step 1 uses the new support-factorization statement; its statement explicitly says that vanishing of all outside stalks gives the canonical closed direct-image isomorphism. Step 2 uses the Mathlib leaf `TopologicalSpace.NoetherianSpace.set` to make the closed subspace Noetherian and uses the existing Krull-dimension definition for the inherited bound. Step 3 applies the existing statement of Proposition 02UZ, which exactly takes a Noetherian space, an integer dimension bound, and an abelian sheaf and returns vanishing above that bound. Step 4 uses the existing 02UV closed-immersion comparison and the Step 1 isomorphism to transfer the vanishing back to `X`. I checked the empty-support case (the restricted sheaf is zero), a zero-dimensional point (all positive cohomology vanishes), and a one-dimensional closed support (vanishing starts in degree two). Every citation quote in `citations.json` is copied verbatim from the cited node statement. The imported item had no proof; I added the four complete steps, synchronized `proof_deps`, filled the blueprint split metadata, and declared the generic 02UZ and 02UV nodes as tool uses.

## What was wrong or incomplete

The item was unsplit despite an existing general Noetherian topological vanishing node. The support-factorization fact was not present in the DAG, so it was added as a statement-only child after the DAG/blueprint searches and Mathlib searches found no equivalent declaration.

## Could not finish

Nothing remains for this split.
