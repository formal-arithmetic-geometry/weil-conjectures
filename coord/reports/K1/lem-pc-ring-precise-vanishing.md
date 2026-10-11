# Stage-1 report: lem-pc-ring-precise-vanishing

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-ring-precise-vanishing.json`: split Tag 064D into three proof steps; no exact Lean declaration and no Mathlib match for the full statement.
- `dag/nodes/sec-picard-framework/lem-pc-ring-projective-into-acyclic-zero.json`: Mathlib leaf for null-homotopy of maps from bounded-above projective complexes to acyclic complexes.
- `citations.json`: verbatim statement quotes for every cited dependency of every step.

## Attachments

None. The slopmaster2 source contains no declaration tagged `(blueprint: lem-pc-ring-precise-vanishing)` and no declaration with the exact arbitrary-abelian-category statement.

## WANTED

None.

## Not duplicates

lem-pc-ring-projective-into-acyclic-zero vs lem-sc-bounded-above-projective-kprojective: the new leaf states the null-homotopy conclusion for a map into an acyclic complex, while the existing leaf states K-projectivity as the Hom-complex acyclicity property.

lem-pc-ring-precise-vanishing vs lem-sc-affine-projective-complex-derived-hom: the item vanishes maps into complexes whose cohomology is zero above a cutoff in an arbitrary abelian category; the existing node is a one-point ringed-space derived-Hom computation with a bounded-below target.

## Review by K1

I read the full Stacks Project proof of Tag 064D in `/home/ubuntu/c1-stacks-review/derived.tex`, lines 6749--6900. The statement's three hypotheses match the source exactly: bounded projective source, source zero below `n`, and target cohomology zero in degrees at least `n`. I also checked the derived-category definition node to confirm that `Q` is the localization used by the statement.

Step 1 uses the existing Mathlib leaf `lem-pc-ring-derived-map-representative`; its statement explicitly gives the bijection between homotopy-category maps from `P` and derived-category maps from `Q(P)`. Step 2 uses `lem-sf-derived-truncation-triangle`, whose statement supplies the distinguished triangle with lower and upper truncation cohomology bounds, and `lem-weil-pbc-hom-into-triangle-exact`, whose statement gives exactness of `Hom(W,-)` on a distinguished triangle. The hypothesis `H^i(K)=0` for `i >= n` makes the upper truncation acyclic, while the lower truncation is zero in degrees where `P` can be nonzero only after the cutoff.

Step 3 uses the new Mathlib leaf `lem-pc-ring-projective-into-acyclic-zero`; its declaration search found `CochainComplex.IsKProjective.homotopyZero`, with bounded-above projectivity supplied by `CochainComplex.isKProjective_of_projective`. The lower-target vanishing is degreewise from `P^i=0` for `i<n` and the canonical lower truncation's support in degrees below `n`; the exact Hom sequence then yields vanishing for `K`. I tested the zero complex and a one-term projective complex at `n=0`, where both conclusions reduce directly to the stated degree support and acyclicity conditions.

I searched the whole DAG and blueprint for Tag 064D, the projective-to-acyclic fact, and precise-vanishing keywords. The existing neighboring split had already created the same Tag 064D node, so I reused its statement rather than duplicating it. I corrected the Mathlib search record for the new leaf to preserve the actual search outputs, including the unavailable LeanSearch service and the rejected Loogle pattern.

## What was wrong and what changed

The item was unsplit and had no proof dependencies. I added the complete three-step Stacks argument and one strictly smaller Mathlib leaf. No statement was weakened or changed.

## Unfinished

Nothing.

## Second reading by K1

- Item statement: checked against Stacks Tag 064D (`lemma-precise-vanishing`) in `derived.tex`, lines 6872--6885; all hypotheses and both vanishing conclusions agree, including the zero-complex and one-term projective cases.
- Step 1: checked against the Tag 064D proof and the complete statement of `lem-pc-ring-derived-map-representative`; the comparison bijection supplies exactly the reduction from derived morphisms to homotopy-class chain maps.
- Step 2: checked against Remark Tag 08J5 and the complete statements of `lem-sf-derived-truncation-triangle` and `lem-weil-pbc-hom-into-triangle-exact`; the standard truncation complexes, acyclicity of the upper truncation, and exact Hom reduction are now stated explicitly.
- Step 3: checked against the two endpoint arguments in the Tag 064D proof and the complete statement of `lem-pc-ring-projective-into-acyclic-zero`; degreewise zero maps to the lower truncation and null-homotopy into the acyclic upper truncation give the required Hom vanishing.
- New node `lem-pc-ring-projective-into-acyclic-zero`: checked B1--B7, the Mathlib declaration and recorded searches, and the zero and one-term projective edge cases; verdict: exact Mathlib leaf and strictly smaller than the item.
- No duplicate or blueprint node states the new dependency; searches covered the DAG and imported blueprint, with the item ancestor `lem-sc-finite-duality` and its map-lifting proof place recorded.

Changes made: corrected the item node's `created.item` metadata; replaced the truncation proof wording that conflated derived objects with standard truncation complexes; made the exact Hom use explicit; and replaced partial citation fragments with complete verbatim dependency statements. The worker's first review remains above unchanged.
