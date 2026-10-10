1. Files written: `dag/nodes/sec-picard-framework/lem-pc-base-change-map-cech.json` (statement, split), `dag/nodes/sec-picard-framework/lem-pc-derived-direct-image-composition.json` (statement-only, unsplit, Mathlib no match), and `citations.json`.

2. Attachments: none.

3. WANTED: none.

4. The returned split was repaired at all three points. Step 1 now checks the separated and quasi-compact hypotheses after base change, the affine pullback cover, and the affine pushforward identification. Step 4 no longer treats the conclusion as an elementary expansion: it constructs the termwise Cech representative of the unit, uses the new generic composition statement, applies the derived adjunction and its underived comparison, and identifies the component maps with the affine section maps. The new composition node was searched against the DAG and blueprint before creation; no existing scheme-level derived composition node was found.

## Review by K1

I reread the item, the ancestor `lem-pc-rf-base-change-flat-module`, the blueprint final-comparison passage, and the statements of every cited node. Step 1 uses `lem-pc-cech-resolution` for both complexes, `lem-weil-pbc-separated-base-change` and `lem-pc-quasi-compact-base-change` for the hypotheses on the pullback morphism, and `lem-pc-affine-morphism-hi` for affine pushforward acyclicity and quasi-coherence. The base-change and module-pullback definitions supply the objects and notation. Step 2 uses exactly the affine pullback-sections isomorphism with $V=U_J$ and $U=p^{-1}(U_J)$. Step 3 is the elementary restriction and alternating-sum calculation.

For Step 4 I checked each dependency's statement: `lem-pc-affine-morphism-hi` gives acyclicity of the pulled-back affine terms; `lem-pc-derived-direct-image-composition` gives the required $R(f\circ p)_*\cong Rf_*Rp_*$ identification; `lem-pc-ringed-spaces-derived-adjoint` supplies the $Lg^*\dashv Rg_*$ adjunction; `lem-sc-derived-adjunction-from-underived` supplies the derived adjunction from the underived one; and `lem-weil-pbc-module-pullback-affine-sections` gives the displayed $c_J$. The derived pullback/direct-image definitions provide the canonical first arrow and the functors. The new node is statement-only as required, has the Stacks 0D5T source, and records LeanFinder, Loogle, grep, and LeanSearch searches exactly as run.

I tested the one-open cover and identity-base-change cases: the Cech complex has only degree zero and every $c_J$ is the identity, so the repaired construction specializes correctly. The item and new node parse as JSON, `check_dag.py` reports no cycles, and the return's missing hypotheses and uncited derived composition/adjunction facts are now explicit in the dependencies and citation packet.

## Second reading by K1

- Item statement: checked against the ancestor blueprint final-comparison passage and the Stacks 08IB comparison; the separated, quasi-compact, affine-cover, pullback, and Cech hypotheses and the canonical-map conclusion agree hypothesis by hypothesis.
- Step 1: checked against `lem-pc-cech-resolution`, the separated and quasi-compact base-change nodes, and `lem-pc-affine-morphism-hi`; the base-changed hypotheses, affine intersections, and acyclic pushforward identification are all cited and present.
- Step 2: checked against `lem-weil-pbc-module-pullback-affine-sections` with $V=U_J$ and $U=p^{-1}(U_J)$; the displayed tensor map and its scalar action are exactly the cited statement.
- Step 3: checked directly from the restriction maps and alternating Cech differential definition; the two-line naturality calculation is elementary.
- Step 4: checked against the Cech resolution, affine acyclicity, `lem-pc-derived-direct-image-composition` (Stacks Lemma 20.28.2, Tag 0D5T), the derived adjunction nodes, and the affine section formula; the unit representative, composition isomorphism, adjunction, and component maps are explicitly accounted for.
- New node `lem-pc-derived-direct-image-composition`: statement checked against Stacks Lemma 20.28.2 (Tag 0D5T), including its ringed-space generality specialized to schemes; it is statement-only, self-contained, and not duplicated by the existing coefficient-specific Weil composition node. Small cases (identity morphism and affine identity composition) give the identity isomorphism.

Changes made: removed the sandbox copy of `lem-pc-base-change-map-cech`, which was a verbatim duplicate of the item rather than a strict auxiliary node; retained the item’s repaired four-step proof. Corrected the new node’s source label to the exact Stacks lemma title and tag. The one-open-cover and identity-base-change cases were rechecked: the Cech complex is concentrated in degree zero and every $c_J$ is the identity. Mechanical dry run passed with `deliver.py ... --no-push`.
