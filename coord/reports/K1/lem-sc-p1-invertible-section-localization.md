# Delivery report

Files written:

- `dag/nodes/sec-picard-framework/lem-sc-p1-invertible-section-localization.json` — item split into injectivity and surjectivity steps.
- `dag/nodes/sec-picard-framework/lem-sc-p1-section-restriction-s-torsion.json` — new statement-only kernel lemma; Mathlib search found only structure-sheaf analogues.
- `citations.json` — verbatim citation for the single proof step.
- `report.md` — this report.

Attachments: none.

WANTED: `literature/stacks-project/properties.tex`, Lemma 01PW source text is not present in this checkout; the proof follows the imported Stacks statement and existing reviewed clearing-denominators result.

The item was unsplit and has no exact declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`; only the related `exists_tensorPowSection_eq_restrict` declaration (ClearDenominators.lean:262) exists and is not the same theorem. The existing stronger cohomology node was rejected as a dependency because its affine specialization depends back on this item, creating a cycle. I therefore used the existing reviewed node `lem-pc-section-clearing-denominators` for surjectivity and created one smaller statement-only kernel lemma for injectivity. The required LeanFinder, Loogle, grep, and LeanSearch searches for the new node were run and recorded; LeanSearch was unavailable and Loogle returned a parser error.

## Review by K1

I read the item node, its Picard-framework unit and chapter metadata, the source-repository ProjectiveSpace/ClearDenominators files, and the existing nodes `lem-pc-section-clearing-denominators` and `lem-weil-pbc-nonvanishing-section-trivializes`. The item statement agrees with Stacks 01PW part (2): quasi-compact and quasi-separated X, invertible L, section s, quasi-coherent F, the graded module of all twists, degree-zero localization, and the map sending `t/s^n` to the restriction divided by `s^n`.

Step 1 cites `lem-sc-p1-section-restriction-s-torsion`, whose statement says exactly that a section restricting to zero on `X_s` is killed by a tensor power of s; this gives the localization equivalence relation and hence injectivity. Step 2 cites `lem-pc-section-clearing-denominators`, whose statement gives a global tensor-power lift of every section on `X_s`; dividing by that power gives surjectivity. Each citation quote is copied verbatim from the cited statement, and all hypotheses (quasi-compactness, quasi-separatedness, invertibility, and quasi-coherence) are present in the item and the cited statements. The new node is deliberately statement-only and strictly smaller than the item.

I checked the small edge cases while reviewing the specialization: with `L = O_X` it reduces to ordinary localization on a principal open, and with `s = 0` both the degree-zero localization and sections on the empty nonvanishing locus are zero. The source checkout contains no exact sorry-free declaration for the item, so there is no attachment.
