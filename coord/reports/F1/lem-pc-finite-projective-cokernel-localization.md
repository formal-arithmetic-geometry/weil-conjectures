1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-pc-finite-projective-cokernel-localization.json` (item, statement, split)
- `dag/nodes/sec-abelian-varieties/lem-pc-finite-free-map-residue-localization.json` (new statement node, unsplit, Mathlib no match)
- `citations.json`

2. Attachments:

- No Lean declaration attached; the source repository has no declaration tagged `lem-pc-finite-projective-cokernel-localization`.

3. WANTED:

- None. The cited Stacks source is the algebra lemma Tag 00O0.

4. What was checked and corrected:

- I read the item against Stacks Algebra, Tag 00O0, parts (1) and (3), and checked the imported unit route in `sk-prop-av-cube` and the ancestor `thm-sc-theorem-of-cube`. The item statement has both the injective-fibre/cokernel conclusion and the isomorphism-fibre conclusion required by the source.
- I searched the whole DAG for `00O0`, cokernel-flat, residue-field injectivity, and finite-projective localization. The existing `lem-weil-pbc-finite-projective-prime-local-free` states exactly the needed finite-free localization fact, so I cite it rather than creating a duplicate.
- Step 1 uses that node's explicit conclusion that each finite projective module becomes finite free after localizing at an element outside the prime. Since that element is invertible in the residue field, the fibre hypothesis survives.
- The new node `lem-pc-finite-free-map-residue-localization` records the finite-free matrix argument from Tag 00O0: select an $m\\times m$ minor that is nonzero at the prime in the injective-fibre case, invert it, and use elementary row and column operations to split off an identity block; the remaining coordinates identify the cokernel with a finite free module. In the equal-rank case the same invertible determinant gives an isomorphism.
- I ran LeanFinder, Loogle, grep, and LeanSearch searches for the new node. LeanFinder returned only local-ring and finite-presentation ingredients; Loogle and grep found no exact theorem; LeanSearch was unavailable. These results are recorded verbatim in the node.
- I verified that the new node is a finite-free specialization and therefore is not a duplicate of the projective statement. The item then composes the two principal localizations and explicitly notes that the composite element remains outside the original prime.

## Not duplicates

lem-pc-finite-free-map-residue-localization vs lem-pc-finite-projective-cokernel-localization: the new node is restricted to maps between finite free modules and proves the invertible-minor splitting; the item allows arbitrary finite projective source and target and obtains freeness only after a preliminary localization.
lem-pc-finite-free-map-residue-localization vs lem-pc-hilb-representable: the existing node uses Tag 00O0 only for openness of a surjectivity condition in Hilbert representability, while the new node is the ring-theoretic residue-fibre matrix criterion.
lem-pc-finite-free-map-residue-localization vs lem-sc-finite-locally-free-residue-isomorphism: the existing node is a sheaf-level criterion assuming fibre isomorphisms at every point; the new node is a single-prime ring-level finite-free localization result and includes the injective-fibre/cokernel clause.

## Review by F1

I checked every proof step against the cited node statements. Step 1 cites the existing finite-projective prime-local-free statement and uses exactly its conclusion. Step 2 cites the new finite-free specialization and uses both clauses stated there. The hypotheses are preserved because localization at an element outside the prime does not change the residue field at that prime. I also checked the two edge cases: rank zero (the injective map has zero source and finite-free cokernel equal to the target) and equal source/target rank (the normal form is an identity matrix). The statement, blueprint ancestor, source places, Mathlib searches, proof dependencies, and citation quotes were all synchronized.

## Second reading by F1

- Item statement: checked against Algebra Tag 00O0, Lemma `cokernel-flat`, parts (1) and (3), hypothesis by hypothesis; verdict correct.
- Step 1: checked against `lem-weil-pbc-finite-projective-prime-local-free`; localization away from the prime makes both modules finite free and preserves the residue field; verdict correct.
- Step 2: checked against the finite-free specialization and Tag 00O0's invertible-minor argument; injective fibre gives a free cokernel after localization, and equal-rank isomorphism fibre gives an isomorphism; verdict correct.
- New node `lem-pc-finite-free-map-residue-localization`: checked against Tag 00O0, parts (1) and (3), including the cases $m=0$, $m=n$, and $R$ a field; verdict statement correct and strictly narrower than the item.
- Existing-node search: searched the DAG for Tag 00O0, residue-field injectivity, finite-free maps, and cokernel localization; the only reusable projective-to-free result is `lem-weil-pbc-finite-projective-prime-local-free`.

Changes made: removed the worker's `proof_old` field because an asserted block reduction killing the residual block by localization is not valid in general and an unsplit node must carry a statement only; corrected the finite-free statement to use explicit finite free modules $R^{\\oplus m}$ and $R^{\\oplus n}$ without an irrelevant projective-module citation; updated this review to record the exact source check and the valid minor argument.
