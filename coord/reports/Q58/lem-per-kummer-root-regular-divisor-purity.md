# Stage 1 report: lem-per-kummer-root-regular-divisor-purity

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-kummer-root-regular-divisor-purity.json` — item, statement split into eight proof steps; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-kummer-classifying-purity-criterion.json` — statement-only supporting node; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-kummer-relative-cone-functor.json` — statement-only supporting node; no Mathlib match.
- `citations.json` — verbatim statement quotations for all twenty step citations.

## Attachments

No sorry-free declaration in the reference Lean source states this item or either new supporting node. No attachment was made.

## WANTED

None. The cited ILO XVI source is present in `literature/`.

## What was checked and corrected

The imported item was read together with the ILO XVI Proposition 3.4.5 and Lemmas 3.4.6–3.4.9 passage (printed pages 246–248), the chapter and unit records, and every cited DAG statement. The proof is split into the monic root algebra and finite locally free geometry (steps 1–2), strict-local reduction (step 3), the low-degree Kummer comparison (step 4), the finite-cover relative cone comparison (step 5), the explicit cyclic filtration (step 6), the least nonzero cohomology argument (step 7), and the pointwise-to-global purity conclusion (step 8).

The earlier attempt had an ill-typed filtration child and an overcompressed relative-cone statement. I removed the filtration child and wrote its displayed modules and exact sequences as the elementary step they are; I replaced the relative-cone child by a self-contained statement for a general finite-index slice, including the direct-image permutation module and both derived-section identifications. The Kummer criterion child now records the root tower, its H^0/H^1 comparison, and the shifted-tower cartesian square without claiming the parent purity equivalence. The parent proof uses direct image `g'_*A` (rank ℓ), not inverse image, and does not invoke a false locality principle.

For step 1 I checked the monic quotient basis, finite locally free spectrum, and finite-algebra Noetherianity statements; coefficientwise nonzerodivisor, the quotient identification, and prime lifting are written out. For step 2 I checked the root-local regularity, the etale complement, and the etale regularity base-change statements with the hypotheses `f` nonzero-divisor and `B/(f)` regular; the auxiliary element is explicitly `1`, whose quotient is the empty regular scheme. For step 3 I checked strict-henselization regularity, regularity of the divisor quotient, faithful flatness, flat preservation of injectivity, and the finite-base strict-localization decomposition; the geometric fibre `Ω[u]/(u^ℓ)` has one connected component, so the selected root strict localization is the required one. For steps 4–5 I checked that the criterion node supplies exactly the degree 0/1 comparison and tower square, while the relative-cone node supplies the triangulated functor and finite-cover direct-image comparison. Step 6 is an explicit basis calculation in characteristic ℓ. Step 7 uses only the abstract derived-category triangles, triangulated functor, and long exact cohomology statements; the least-degree induction is spelled out. Step 8 applies the strict-local divisor criterion after the regularity and local-complement identifications, including the empty-divisor case.

I ran LeanSearch, Loogle or LeanFinder, and Mathlib grep searches for the item and each new node; the recorded searches found only unrelated algebraic Kummer, group-cohomology, or general triangulated infrastructure and no matching purity statement. I tested the root-algebra assertions on the empty spectrum, unit parameter, and a strictly henselian DVR, and checked the filtration at ℓ=2 as well as general prime ℓ. Every citation quote in `citations.json` is a verbatim substring of the cited node statement.

## Review by Q58

I reviewed the item and both new nodes against the source and the live DAG before writing this report. The item source is ILO XVI Proposition 3.4.5 with Lemmas 3.4.6–3.4.9, pp.246–248; the two new-node sources are the low-degree/root-tower paragraphs and the finite-cover relative-cone paragraphs in the same pages. Each proof step names every non-elementary statement it takes, and each cited statement was opened and matched to the quoted sentence in `citations.json`. The hypotheses checked include regularity and Noetherianity of `B`, invertibility of ℓ, nonzerodivisor status of `f`, regularity of `B/(f)`, the strict-local hypotheses after base change, finite index of `ℓG`, and bounded-below cohomology for the least-degree argument. I corrected the imported direct/inverse-image error, removed the redundant filtration node, expanded the finite-cover cone statement, and made the pointwise passage use the stated strict-local criterion. The mandated server `check_dag` precheck passed before this report was written.

## What could not be finished

Nothing remains unresolved in the stage-1 split.
