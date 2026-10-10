1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-point-tangent-separation-closed-immersion.json`: repaired item, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-point-tangent-cotangent-surjective.json`: statement-only Tag 0B2E node, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-point-tangent-finite-local-cotangent-surjective.json`: statement-only Tag 0E8M node, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-finite-type-nonclosed-closure-closed-points.json`: statement-only finite-type closure fact, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-point-tangent-closed-fibre-singleton.json`: statement-only closed-fibre singleton fact, no Mathlib match.
- `dag/nodes/sec-picard-framework/thm-sc-proper-finite-fibre-finite-neighbourhood.json`: statement-only Tag 02OH criterion, no Mathlib match.
- `citations.json`: verbatim citations for every step/node use.

2. Attachments: `lem-weil-pbc-closed-point-residue-field-base` is reused for the residue-field step.

3. WANTED: none.

4. The return identified that the old step 4 asserted a coordinate computation without writing its set-theoretic content, and that step 5 incorrectly used the proper-plus-finite-all-fibres criterion while only closed fibres had been established. I added the finite-type closure node and the closed-fibre singleton node, whose statements make the empty-or-singleton conclusion explicit and are cited by both the fibre and stalk steps. I replaced step 5 with Tag 02OH: apply it at each closed point, then use the existing quasi-compact/Kolmogorov closed-point node to show the resulting open neighborhoods cover projective space. I removed `thm-pqf-finite-iff-proper-finite-fibres` from the proof and tool uses. I also added the existing residue-field-base node to step 6 and gave both earlier tangent/cotangent nodes complete `created.by` and `created.date` metadata.

## Review by J1

I reread the item source in Stacks `varieties.tex` Tag 0E8S and the supporting sources: Tag 02O5 for finite-dimensionality, Tag 01W6 for properness, Tag 005E for closed points in quasi-compact Kolmogorov spaces, Tag 0478 and Tag 0A21 for finite-type Jacobson and dimension behavior, Tag 02OH for finite-over-a-neighborhood, Tag 0B2E for tangent/cotangent duality, Tag 0E8M for the finite-local Nakayama criterion, and Tag 00FV/01TB as represented by `lem-weil-pbc-closed-point-residue-field-base`.

Step 1 uses exactly the finite-dimensional global-sections statement of `lem-pc-coherent-hi`. Step 2 uses the three cited definition nodes for generation, the projective morphism, and the pullback twist. Step 3 uses `lem-weil-pbc-proper-to-separated` for properness of the map to projective space. Step 4 now cites `lem-sc-point-tangent-closed-fibre-singleton`; that statement explicitly supplies the empty-or-singleton fibre equality, while its dependencies and the step citations record the closed-point existence and infinitely-many-specializations facts that rule out a nonclosed point. Step 5 cites the exact Tag 02OH statement and the existing closed-point node, applying the neighborhood criterion at every closed point and ruling out a nonempty closed complement. Step 6 cites the same singleton equality to identify the pushforward stalk with `O_{X,x}`, and cites `lem-weil-pbc-closed-point-residue-field-base` for both residue fields being `k`; the finite stalk map follows from step 5. Steps 7 and 8 use the two existing statement-only tangent/cotangent nodes, and step 9 is the definition of very ampleness.

I checked that every new node is self-contained, statement-only, has the correct Stacks source and blueprint provenance, includes all three required Mathlib search records, and has `created.by = worker`, the delivered item, and date `2026-10-10`. I checked all citation quotes against the node statements and removed the obsolete finite-fibre theorem from `proof_deps` and `tool_uses`.
