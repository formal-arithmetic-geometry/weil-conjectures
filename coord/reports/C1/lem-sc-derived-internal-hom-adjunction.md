1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-derived-internal-hom-adjunction.json`: repaired concrete four-step split; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-derived-hom-tensor-total.json`: Stacks 0A8I statement-only lemma; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-rhom-kflat-kinjective.json`: Stacks K-flat/K-injective RHom comparison; no Mathlib match.

2. Attachments: none.

3. WANTED: none.

4. The returned abstract node was deleted because it merely restated the item and its claimed Lean source did not identify the concrete RHom model or symmetry. The item now follows Stacks 08DJ: choose P, L' and I; identify Hom(P,Hom(L',I)) with Hom(Tot(P tensor L'),I) by 0A8I; use the K-flat/K-injective comparison; then use the sheaf-complex symmetry with Koszul signs for 0FPB. The item statement was preserved.

## Review by C1

I read the item and its `lem-sc-finite-duality` blueprint ancestor, the returned files, and the cited definitions for K-flat complexes, K-flat resolutions, K-injective complexes, derived internal Hom, total tensor complexes, and sheaf-module tensor-Hom closure. I checked each proof step against the exact statement of every cited node and recorded verbatim quotes in `citations.json`. Step 1 verifies the Grothendieck and monoidal-closed hypotheses and the chosen resolutions. Step 2 uses the new 0A8I node and the total-complex definition to pass to H^0. Step 3 uses the new K-flat/K-injective node to establish K-injectivity and independence of representatives. Step 4 checks the sheaf-level symmetry and the K-flat quasi-isomorphism invariance before descending to the derived category. I searched the DAG and blueprint for duplicates and found none; the Mathlib searches for the item and both new nodes were run with LeanFinder, Loogle, grep, and LeanSearch (unavailable), with results recorded in the node files. I corrected the original abstract split, added the two concrete statement-only lemmas, repaired notion citations, and declared the off-unit Grothendieck and tensor-closed facts as generic tool uses.

## Not duplicates

lem-sc-derived-hom-tensor-total vs lem-sc-derived-internal-hom-adjunction: the new node is the chain-level 0A8I isomorphism, while the item is the derived-category bijection and symmetry.

lem-sc-rhom-kflat-kinjective vs lem-sc-derived-internal-hom-adjunction: the new node is the K-flat/K-injective comparison lemma, while the item assembles it with resolutions and total-tensor adjunction.

## Second reading by C1

Re-read all four item steps and both new statements against their Stacks places and exact DAG citations. Confirmed that no abstract restatement remains, the symmetry clause is supplied at sheaf-complex level, all hypotheses used by each step occur in cited statements, and the dry run passes.

## Second reading by C1

- Item statement: checked against cohomology.tex Tag 08DJ equation (1) and Tag 0FPB; the scheme, derived-category, K-flat model, functoriality, and symmetry clauses agree hypothesis by hypothesis; verdict pass.
- Step 1: checked against Tags 08DJ and 0A8T plus the cited resolution, K-injective existence, and sheaf tensor-closed statements; the chosen representatives and ambient hypotheses are present; verdict pass after the later K-injectivity use was made explicit in Step 2.
- Step 2: checked against Tag 0A8I and the definition of derived internal Hom; it now cites the K-flat/K-injective node before taking H^0, so the represented complex is admissible; verdict fixed.
- Step 3: checked against Tag 0A8T and the derived internal-Hom well-definedness clause; the quasi-isomorphism direction and representative independence agree; verdict pass.
- Step 4: checked against Tag 0FPB, the symmetric monoidal sheaf-module statement, the K-flat definition, and the K-flat resolution; Koszul signs and preservation of quasi-isomorphisms are explicitly supported; verdict fixed.
- New node lem-sc-derived-hom-tensor-total: checked against Tag 0A8I (cohomology-lemma-compose), with all complex and ringed-site notions cited and TeX formatted; verdict pass.
- New node lem-sc-rhom-kflat-kinjective: checked against Tag 0A8T; repaired it to introduce the site, ring sheaf, both complexes, the quasi-isomorphism, and all defining notions; verdict fixed.

Changes made: corrected the 0A8T source label and made its statement self-contained; added its citation to Step 2 and moved the admissibility justification before the H^0 argument; added the K-flat definition citation to Step 4 and citations.json; refreshed the corresponding verbatim citation quotes. The two supporting nodes remain genuine statement-only facts rather than restatements or duplicates. Small cases (the one-point ringed site and zero complexes) leave the adjunction and symmetry as the ordinary tensor-Hom bijection and zero-complex identity.
