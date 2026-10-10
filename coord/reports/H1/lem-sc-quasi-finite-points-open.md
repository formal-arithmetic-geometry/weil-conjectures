1. Files written

- `dag/nodes/sec-picard-framework/lem-sc-quasi-finite-points-open.json`: item, statement node, Mathlib candidate retained (not an exact leaf).
- `citations.json`: verbatim citations for all non-elementary step uses.

2. Attachments

None.

3. WANTED:

None. The Stacks source is cited by the existing project literature convention; no new document was needed.

4. What was wrong or incomplete

The imported item had no proof and was `unsplit`. The proof now makes the affine reduction explicit, uses the existing ring-level Tag 00QA openness node, identifies the resulting basic open with an affine open of the scheme, and separately proves the restriction is locally quasi-finite. The Mathlib candidate `Scheme.Hom.isOpen_quasiFiniteAt` was not promoted to a leaf because it requires Mathlib's `LocallyOfFiniteType` and uses Mathlib's `QuasiFiniteAt`, which is not definitionally the Stacks notion in the item.

5. What I could not finish, and why

Nothing remains unfinished.

## Review by H1

I read the item node, its blueprint ancestor `lem-sc-degree-2g1-very-ample`, the Stacks Tag 01TI source reference, and each cited node. Step 1 uses the exact affine-local witness in `pqf-def-quasifinite`; step 2 uses the exact basic-open conclusion of `lem-weil-pbc-ring-quasi-finite-locus-open`; step 3 uses the canonical affine open immersion and point correspondence in `lem-weil-pbc-affine-open-spec-points`, then applies the definition to the localized ring map supplied by step 2. Step 4 is the elementary union argument. Step 5 uses the definition of locally quasi-finite and the statement of `lem-weil-pbc-lqf-restriction-to-opens`. I checked that every cited node says the fact used and recorded each quote in `citations.json`. I also ran LeanFinder, Loogle, LeanSearch, and Mathlib grep searches for the item; LeanSearch was unavailable, while the other searches found only related Mathlib notions, so the item remains an unsplit Stacks statement rather than a Mathlib leaf.
