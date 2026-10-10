Files written:

- `dag/nodes/sec-picard-framework/lem-sc-derived-hom-projective-resolution.json` — statement, split proof, no new nodes, Mathlib generalization only.
- `citations.json` — verbatim statement quotes for all cited steps.

Attachments:

- None. No sorry-free project declaration in `WeilConjectures/` states this item.

WANTED:

- None. The cited Stacks source path is represented in the project literature metadata; the proof is written directly from Tag 06XR.

What was wrong or incomplete:

- The imported item had an empty proof and `unsplit` status despite being a required input of the already split stalk-localization lemma. I supplied the missing projective-resolution argument, set `proof_deps` to the derived internal-Hom definition, and marked the item `split`.
- Mathlib searches found only the more specialized projective-resolution Ext/K-projective API, so the item is not a Mathlib leaf. No duplicate DAG node or matching blueprint node was found.

## Review by K1

I read the item source metadata and the Stacks Derived Categories Lemma 06XR route used by the parent stalk-localization node. The statement's hypotheses are unchanged: a ring, two modules, a bounded-above projective complex with a quasi-isomorphism to the first module in degree zero, and the derived internal-Hom definition. Step 1 uses the definition's Hom-complex and derived-category interfaces and spells out why bounded-above projectives are K-projective, so the ordinary Hom complex computes the derived Hom. Step 2 checks the degreewise product totalization and the boundedness/concentration hypotheses. Step 3 applies cohomology and records the canonical, resolution-independent comparison in every integer degree. I opened `def-pur-derived-internal-hom.json` and copied the cited Hom-complex and localization sentences verbatim into `citations.json`; each step's `uses` agrees with those quotes. I searched the whole DAG and blueprint for projective-resolution/RHom duplicates and found none. Required LeanFinder, Loogle, grep, and LeanSearch searches were run on 2026-10-11; the two LeanSearch requests were unavailable and are recorded as unavailable, while the other searches returned only general Mathlib infrastructure. Small checks include $E^\\bullet=F[0]$ when $F$ is projective (ordinary Hom is recovered), the zero module, and negative degrees for modules concentrated in degree zero. No statement or hypothesis was changed.

## Second reading by K1

- Item statement: checked the ring/module, bounded-above projective, quasi-isomorphism, and all-integer hypotheses against Stacks More on Algebra Tag 0A5W and Derived Categories Tag 06XR(2); verdict: mathematically consistent.
- Step 1: checked K-projectivity against Mathlib `CochainComplex.isKProjective_of_projective` and the RHom construction in Tag 0A5W; verdict: dependency now explicit.
- Step 2: checked the product Hom-complex formula against `def-pur-derived-internal-hom` and the degree-zero target; verdict: no longer marked elementary and the degree calculation is written out.
- Step 3: checked cohomology and resolution independence against the derived-category functoriality in `def-pur-derived-internal-hom`; verdict: canonicality is stated with its reason.
- New node `lem-sc-bounded-above-projective-kprojective`: checked self-contained statement, TeX, definition citation, Mathlib declaration/file/line, and LeanFinder/Loogle/grep searches; verdict: exact one-line specialization, status `mathlib`.
- Small cases checked: zero modules, a projective module with $E^\\bullet=F[0]$, and negative degrees for modules in degree zero; all agree.

Changes: corrected the source place to Tags 0A5W and 06XR(2), added the Mathlib K-projective leaf, cited it in all proof dependencies, repaired the Hom-complex citation, and expanded the non-elementary degree and canonicality arguments.
