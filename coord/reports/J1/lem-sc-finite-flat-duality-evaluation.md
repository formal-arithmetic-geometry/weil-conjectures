# lem-sc-finite-flat-duality-evaluation

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-finite-flat-duality-evaluation.json`: repaired item split; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-finite-duality-derived-hom.json`: new statement-only canonical finite-duality node; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-affine-derived-concentration.json`: new statement-only affine concentration node; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-finite-locally-free-derived-hom.json`: new statement-only finite-locally-free derived-Hom node; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-finite-pushforward-locally-free.json`: new statement-only finite-flat pushforward local-freeness node; no Mathlib match.

## Attachments

None.

## WANTED

None.

## Statement changes

The item names the canonical isomorphism as `Phi` so its final module-linearity formula is well-defined. The generic finite-duality helper is restricted to bounded-below `D+_QCoh` objects. The locally-free helper uses an open cover with locally constant finite rank. The pushforward helper explicitly marks `finite`, `flat`, and `locally of finite presentation` with their definition dependencies.

## What was wrong

The returned split had two helper nodes that merely relabelled the item, and its counit node allowed an arbitrary linear isomorphism rather than the canonical duality isomorphism. The replacement generic node has the bounded-below hypothesis. The split adds statement-only nodes for sheaf-level finite-flat pushforward local freeness, affine concentration, and derived Hom from a finite locally free sheaf. The return also identified incorrect source metadata and a stale off-unit rank citation; those are corrected here. The finite-duality source now uses Tags 0AX2 and 0AX3 in both the item source and proof origin.

## Review by J1

I read the item and its blueprint ancestor `lem-sc-finite-duality`, the finite-presentation node, and the Stacks sources for Tags 0AX2, 0AX3, 0AVW, 08I8, 01XC, 08DQ, 0FKW, 02KB, and 04MH. Step 1 uses the canonical derived-Hom and evaluation-at-1 clauses stated by `lem-sc-finite-duality-derived-hom`. Step 2 uses the finite-presentation statement, the new pushforward-local-freeness statement with explicit finite/flat/finite-presentation hypotheses, and the locally-constant-rank derived-Hom statement. Step 3 uses the affine derived-concentration statement, whose source is now `perfect.tex` with the required affine and vanishing tags. Step 4 is the elementary module-linearity identity for the named `Phi`. I checked rank-zero and rank-one cases, disconnected bases with varying locally constant rank, and the identity finite-flat map.

For return point 1, this report lists only the five node files delivered and its review describes only checks made on those files; it does not claim that a citation manifest or maintainer-created fields were committed. For point 2, the pushforward statement and `stmt_deps` now cite `def-weil-finite-integral-morphism`, `def-weil-flat-morphism`, and `def-sbc-locally-finite-presentation`. For point 3, the derived-Hom node cites Tag 08DQ in `cohomology.tex`. For point 4, the affine node cites `perfect.tex` and includes Tags 0AVW, 08I8, and 01XC. For point 5, both item source locations use Tags 0AX2 and 0AX3. For point 6, `split_report.tool_uses` retains only the finite-presentation tool used by step 2; the stale rank citation is removed. New nodes retain the delivered `created` item field for the maintainer to fill on merge.
