# Stage-1 report

1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-derived-internal-hom-restrict-open.json` — item, statement, four proof steps, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-derived-k-injective-restrict-open.json` — statement-only dependency, no Mathlib match.
- `citations.json` — verbatim statement excerpts for every cited node and step.

2. Attachments: none.

3. WANTED: `literature/stacks-project/cohomology.tex`, Lemma 08DL (restriction of derived internal Hom), for `lem-sc-derived-internal-hom-restrict-open`.

WANTED: `literature/stacks-project/cohomology.tex`, Lemma 08BS (restriction of K-injective complexes), for `lem-sc-derived-k-injective-restrict-open`.

4. No statement or blueprint error was found. The source tex files are not present in this checkout, so the split follows the imported Stacks labels and the existing definition node `def-pur-derived-internal-hom`.

## Review by M1

I searched the source tree and the DAG for the item tag, its title, 08DL, and 08BS. The source tree contains no declaration tagged for this item; the only related internal-Hom code is implementation infrastructure and does not state the target. The DAG has no general open-restriction K-injective node, so I created the focused statement-only node `lem-sc-derived-k-injective-restrict-open`; the etale-specific injective restriction node is a different statement and was not reused.

Step 1 uses `def-pur-derived-internal-hom` for the K-injective model of derived Hom and `prop-pur-kinjective-resolutions-exist` for existence of a functorial K-injective resolution. Step 2 uses the new node exactly for preservation of K-injectivity under termwise open restriction and the definition node for the resulting Hom model. Step 3 uses the definition's explicit Hom-complex terms and differential; the termwise restriction/Hom identification is the 08DL calculation. Step 4 uses the derived-category localization and the functoriality clause in `def-pur-derived-internal-hom` to descend the complex isomorphism and identify it as canonical. I checked each citation against the node statement and recorded verbatim excerpts in `citations.json`.

I ran LeanFinder, Loogle, and Mathlib grep searches for both the item and the new node. LeanFinder returned only underived SheafOfModules or unrelated condensed internal-Hom results; Loogle's supplied patterns were rejected with zero hits and are recorded as unavailable; grep found no matching restriction theorem. Small cases checked: $U=X$ gives the identity, and $U=\\varnothing$ gives the zero restriction and zero Hom comparison.

5. Nothing remains unfinished in the split. The dry run is the next required check.

## Not duplicates

lem-sc-derived-k-injective-restrict-open vs lem-sc-derived-internal-hom-restrict-open: the new node states preservation of K-injectivity under termwise restriction to an open, while the existing item states the resulting canonical derived internal-Hom isomorphism; Tag 08BS is an input lemma of the item's Tag 08DL source, not the item's conclusion.

## Second reading by M1

- Item statement: checked against `cohomology.tex` lines 10639-10650, `lemma-restriction-RHom-to-U` (08DL); same ringed-space, arbitrary derived objects and open, with a canonical isomorphism in place of the source's equality of canonically constructed objects. For `U = X` it is the identity, and for `U = empty` both Hom complexes are zero.
- Step 1: `def-pur-derived-internal-hom` supplies the K-injective Hom-complex model and `prop-pur-kinjective-resolutions-exist` supplies a functorial resolution; both apply to the ringed space's site of opens. Verdict: valid.
- Step 2: `lem-sc-derived-k-injective-restrict-open` states exactly the K-injectivity needed on `U`; the resolution remains a quasi-isomorphism because restriction to an open is exact, term by term. This is immediate on every stalk in `U`. Verdict: valid.
- Step 3: checked against `def-pur-sheaf-hom` and `def-pur-hom-complex` as well as 08DL. On each `V` open in `U`, Hom sections agree; the indexed product is sectionwise and the differential uses the same component maps. Verdict: valid after expanding this calculation and citing both definitions.
- Step 4: `def-pur-derived-internal-hom` identifies the two models and states independence of representative and resolution. The isomorphism of Step 3 is natural under restriction and hence canonical. Verdict: valid after spelling out these identifications.
- New node `lem-sc-derived-k-injective-restrict-open`: checked hypothesis by hypothesis against `cohomology.tex` lines 7839-7853, `lemma-restrict-K-injective-to-open` (08BS). It is statement-only, self-contained, cites its notion definitions, and uses TeX once. Its source tag and label agree. For `U = X` it is the identity; for `U = empty` the restricted zero complex is K-injective; for a one-point field space restriction is either case. Verdict: true and needed.
- Existing-node and Lean audit: searched DAG for 08BS and K-injective restriction, the whole blueprint for 08BS and K-injective restriction, and slopmaster2 for corresponding declarations; no duplicate or closed declaration. The existing etale-site restriction node has a different scope. Re-ran LeanFinder and Loogle with different wording and Mathlib grep; no matching Mathlib open-restriction declaration.
- Changes: cited the sheaf-Hom and Hom-complex definition nodes at Step 3, expanded its sectionwise product and differential calculation, clarified Step 4's naturality, and updated `citations.json`. The source TeX was located at `/home/ubuntu/c1-stacks-review/cohomology.tex`; the first worker's WANTED note described its earlier availability and remains as history.
