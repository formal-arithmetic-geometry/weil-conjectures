Files written:
- `dag/nodes/sec-picard-framework/lem-sc-derived-hom-finite-free-model.json` (split statement)
- `dag/nodes/sec-picard-framework/lem-sc-bounded-below-injective-resolution.json` (new unsplit statement; no Mathlib match)
- `dag/nodes/sec-picard-framework/lem-sc-bounded-above-finite-free-hom-acyclic.json` (new unsplit statement; no Mathlib match)
- `dag/nodes/sec-picard-framework/lem-sc-kinjective-quasi-iso-comparison.json` (new Mathlib leaf; `CochainComplex.IsKInjective.Qh_map_bijective`, line 52)

Attachments: none.

## Not duplicates

lem-sc-bounded-above-finite-free-hom-acyclic vs lem-sc-derived-hom-finite-free-model: the new node states only acyclicity of Hom against an acyclic second complex; the item additionally identifies the resulting complex with derived internal Hom under a quasi-isomorphism.
lem-sc-bounded-above-finite-free-hom-acyclic vs lem-sc-derived-internal-hom-stalk-localization: the new node is a general ringed-site Hom-acyclicity lemma, while the existing node is a Noetherian-scheme stalk identification and does not state Hom-acyclicity.
lem-sc-bounded-above-finite-free-hom-acyclic vs lem-sc-ext-stalk-localization: the new node concerns total sheaf Hom complexes; the existing node concerns localization of Ext stalks and does not state the bounded-above Hom calculation.
lem-sc-bounded-below-injective-resolution vs lem-weil-derived-limit-existence: the new node constructs a bounded-below injective resolution of a bounded-below module complex; the existing node concerns derived inverse limits.
lem-sc-bounded-below-injective-resolution vs prop-weil-pbc-rlim-functoriality: the new node concerns injective resolutions, while the existing node concerns functorial derived inverse limits.
lem-sc-bounded-below-injective-resolution vs prop-weil-pbc-derived-inverse-limit-computation: the new node concerns bounded-below injective replacements, while the existing node computes derived inverse limits.
lem-sc-bounded-below-injective-resolution vs prop-pur-kinjective-resolutions-exist: the new node adds bounded-below support and termwise injectivity for a bounded-below input; the existing node is the broader existence statement for etale module complexes.
lem-sc-bounded-below-injective-resolution vs def-pur-derived-internal-hom: the new node is a theorem about bounded-below replacements; the existing node only defines derived internal Hom and assumes K-injective replacements.
lem-sc-bounded-below-injective-resolution vs prop-weil-pbc-kinjective-resolutions-exist: the new node specializes to ringed-site modules and records bounded-below support; the existing proposition is the general etale-module existence theorem.
lem-sc-bounded-below-injective-resolution vs lem-weil-pbc-kinjective-functorial-existence: the existing node gives a functorial K-injective replacement with no bounded-below or termwise-injective conclusion; the new node supplies those extra properties for bounded-below input.
lem-sc-bounded-below-injective-resolution vs def-pur-kinjective-complex: the new node asserts existence of a bounded-below resolution; the existing node only defines K-injectivity.

WANTED: none.

The item had no matching sorry-free project declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`. I read the imported target and its blueprint ancestor `thm-sc-p1-duality`; the source route is Stacks Tag 0GM8, case (2), together with sites-cohomology Section 08J7 and Lemma 0A95. The target statement is unchanged.

The first new node records the bounded-below injective resolution used for the bounded-below second complex, from Stacks 07A5 and Theorem 079P. The second records the finite-product totalization fact from Tag 0GM8: Hom from a bounded-above finite-free complex sends a bounded-below acyclic complex to an acyclic total Hom complex. The third new node is the exact Mathlib K-injective comparison declaration. I searched the whole DAG and blueprint for all three ingredients and found no duplicate.

Step 1 uses exactly the resolution and K-injectivity asserted by the first new node. Step 2 applies exactly the second node to the cone of the resolution map; the cone is bounded below and acyclic by the definitions of cone, bounded-below, and quasi-isomorphism. Step 3 uses the definition of derived internal Hom and `lem-sc-kinjective-quasi-iso-comparison`; its cited statement gives the Hom bijection induced by precomposition with a quasi-isomorphism into a K-injective target. The finite-free hypothesis is used only in Step 2, and the bounded-below hypothesis on `G` is used to obtain the bounded-below resolution and cone.

Small checks: for `E` concentrated in degree zero equal to `\\mathcal O_U`, the assertion reduces to the quasi-isomorphism `G -> I`; for the zero complex, both Hom complexes are zero; for a bounded finite free complex, the totalization has finite products in every degree.

## Review by M1

I checked the target source and blueprint text, searched the project Lean source for the item tag and its mathematical keywords, and found no exact declaration to attach. I read the statements of every cited DAG node. The three new statements are strict ingredients rather than restatements: one supplies a bounded-below K-injective resolution, one supplies acyclicity preservation for the Hom total complex, and the Mathlib leaf supplies the K-injective Hom comparison. Each proof step cites the statement it actually consumes, with exact passages recorded in `citations.json`. Mathlib searches were executed and recorded for each new node; LeanSearch was unavailable and recorded as such. No source or statement error was found.

What could not be finished: no Lean compilation is permitted at stage 1, so this delivery contains natural-language DAG statements only.

## Second reading by M1

- Item statement: checked against Stacks Tag 0GM8 (Lemma 20.51.4, case (2)), Tag 08J7 (Section 21.35), and Tag 0A95 (Lemma 21.34.7); hypotheses on bounded-above finite-free $E$, bounded-below $G$, and the quasi-isomorphism $E\to K$ are retained.
- Step 1: checked against the statements of `lem-sc-bounded-below-injective-resolution` and its Tags 07A5 and 079P source; the cited resolution supplies exactly the replacement used.
- Step 2: checked against `lem-sc-bounded-above-finite-free-hom-acyclic`; the cone is the bounded-below acyclic input and finite freeness is used only here.
- Step 3: checked against `def-pur-derived-internal-hom` and the exact Mathlib declaration `CochainComplex.IsKInjective.Qh_map_bijective`; the step now uses localization bijectivity rather than an incorrectly stated precomposition theorem.
- `lem-sc-bounded-below-injective-resolution`: self-contained ringed-site/module hypotheses and K-injective conclusion checked; tested on the zero complex and a complex concentrated in degree zero.
- `lem-sc-bounded-above-finite-free-hom-acyclic`: self-contained boundedness, finite-rank freeness, and acyclicity checked; tested on the zero complex and a one-term free complex.
- `lem-sc-kinjective-quasi-iso-comparison`: declaration, file, and lines 41--46 checked directly in Mathlib; statement is now an exact specialization of `Qh_map_bijective`.
- Changes: corrected the target's `created.item`; replaced prose source locations by Stacks tags and labels; corrected the Mathlib leaf and its citation; updated Step 3 and `citations.json`; recorded the new semantic search in `searches.jsonl`.
