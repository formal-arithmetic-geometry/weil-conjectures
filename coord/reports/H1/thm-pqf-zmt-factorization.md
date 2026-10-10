# Stage 1 report: thm-pqf-zmt-factorization

## Files written

- `dag/nodes/sec-nagata-compactification/thm-pqf-zmt-factorization.json`: split statement.
- `dag/nodes/sec-nagata-compactification/pqf-lem-normalization-open.json`: new unsplit statement-only node; Mathlib partial match.
- `citations.json`: verbatim step citations.

## Attachments

None. The project declaration `AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite` reaches the sorried declaration `AlgebraicGeometry.Scheme.Hom.exists_finiteApproximation_of_isIntegralHom`, so it is not an attachment.

## Not duplicates

pqf-lem-normalization-open vs thm-pqf-zmt-factorization: the item states the final existence of a finite factorization, while this node states the separate relative-normalization construction and its integral and open-immersion properties.

pqf-lem-normalization-open vs thm-pqf-immersion-descent: the descent node assumes a relative normalization and only states descent to a finite stage; it does not state that the normalization morphism is integral or give the canonical construction.

## WANTED

None; the cited Stacks tags and blueprint source are present in the repository metadata.

## Review by H1

I read the item and its blueprint proof in `thm-pqf-zmt-factorization.md`, the existing `thm-pqf-immersion-descent` statement, and the source declarations in `ZariskisMainTheorem.lean` and `Normalization.lean`. The source theorem's proof has exactly the three substantive dependencies recorded here: relative normalization, the existing general finite-approximation node, and descent to a finite stage. I checked the normalization node against Tags 03GW and 02LR and recorded the two Mathlib component instances; I checked the finite-approximation citation against the existing node's full statement and Tag 09YZ provenance. Every proof step cites a node whose statement supplies the quoted fact in `citations.json`. The hypotheses used in the descent step are the quasi-compact open immersion and the finite-stage limit in the cited statements. The final finiteness step uses only the convention node's definition of finite and the closed-immersion conclusion from descent; composition is a two-line elementary argument. I tested the edge case of an identity morphism (normalization and factorization can be identities) and the affine finite case (the finite approximation can be the single finite stage). I did not attach the existing Lean theorem because its transitive sorry map contains the finite-approximation theorem.

## What was wrong or corrected

The imported item had an empty proof despite listing the three blueprint stages and had proposed an attachment to a theorem resting on a sorry. I preserved the target statement, made the blueprint provenance explicit, and split out the two missing intermediate inputs without duplicating the existing descent node.

## Second reading by H1

- Step 1 checked against Stacks More on Morphisms Lemma 37.43.2 (Tag 02LR) and the relative-normalization node; verdict: the integral factorization and quasi-compact open immersion are stated by the cited input.
- Step 2 checked against the full statement of `lem-weil-pbc-integral-morphism-limit-of-finite` (Limits Tag 09YZ); verdict: the limit, affine transitions, and finite stages used by the step are all present.
- Step 3 checked against the full statement of `thm-pqf-immersion-descent`; verdict: its hypotheses and the descended open and closed immersions match the hypotheses in force.
- Step 4 checked against the finite-morphism convention and the descent statement; verdict: the affine quotient argument makes closed immersions finite, finite morphisms compose, and the corrected composite is `p \\circ j = f`.
- `pqf-lem-normalization-open` checked against Tag 02LR, the definition node `lem-weil-pbc-relative-normalization`, and the three recorded Mathlib searches; verdict: self-contained, distinct from the final factorization, and no unsupported local-section clause remains.

Changes made: repointed the normalization node to the Stacks tag and its definition node, removed its unsupported extra local-sections assertion, added the existing relative-normalization dependency, and repaired the final proof step's composition order and elementary justification.
