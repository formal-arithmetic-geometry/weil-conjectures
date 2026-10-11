Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-derived-functor-shift-05su.json` — statement node, split; no new nodes and no Mathlib leaf.
- `citations.json` — verbatim citations for every proof-step dependency.

Attachments: none.

WANTED: `literature/stacks-project/derived.tex`, Lemma 05SU(2), because the checked-out literature directory does not contain the Stacks TeX source; the source was read from the local Stacks review copy at `/home/ubuntu/c1-stacks-review/derived.tex`.

What was wrong or incomplete: the imported item had no proof steps or proof dependencies. The Stacks lemma itself has an omitted proof, so I supplied the categorical transport argument while preserving its exact statement. No duplicate supporting node was created: the saturated-localization, triangulated-category, and essentially-constant-pro-diagram definitions already state the needed hypotheses.

What could not be finished: no Lean declaration exists for this abstract Stacks 05SU statement, and LeanSearch was unavailable; this is recorded in the node's searches.

## Review by F1

I read the item, the unit route, the saturated localization definition, the triangulated-category definition, and the Stacks source at `derived.tex` lines 4657–4676. Step 1 uses the existing MS5 clause and the existing statement that the shift is an additive automorphism; those give the equivalence between denominator categories by shifting arrows and applying the inverse shift. Step 2 uses the exact-functor shift isomorphism stated in the triangulated-category node and the cone/retraction/factorization clauses of the essentially-constant pro-diagram definition; transporting each clause through the two equivalences preserves essential constancy. Step 3 uses the same factorization clause and applies the construction with `-n` to obtain the iff and the canonical value isomorphism. I checked that the item hypotheses supply triangulated categories, an exact functor, and MS5, and that every cited node's statement contains the quoted fact in `citations.json`. I also checked the small case `n = 0`, where the denominator equivalence and canonical isomorphism are identities. The only correction to the imported node was adding these proof steps, dependencies, source origin, blueprint split report, and accurate search records.

## Second reading by F1

Step 1 checked against Stacks Tag 05R2/MS5 and the existing triangulated-category shift definition; the inverse shift gives the reverse implication and the equivalence preserves commuting triangles. Verdict: correct and elementary.
Step 2 checked against the exact-functor shift isomorphism, the full cone/retraction/factorization definition of essential constancy, and the pro-Hom-colimit lemma; transporting this data through the denominator equivalence preserves essential constancy. Verdict: correct, non-elementary, with the canonical-value dependency now explicit.
Step 3 checked against the same essential-constancy clauses and the pro-Hom-colimit uniqueness mechanism; applying the construction at `-n` gives the iff, and the two value maps are canonically inverse. Verdict: correct.
The item statement was checked clause by clause against `derived.tex`, Lemma `05SU` (label `lemma-derived-shift`), clause (2), including the hypotheses in Situation `05S8`; `n = 0` gives identities, and zero objects satisfy the construction vacuously. No new nodes were created, so B1–B7 and duplicate-node checks are vacuous; existing supporting nodes were searched by id and keywords. Changed the two transport steps from `elementary: true` to non-elementary and added `lem-pc-essentially-constant-pro-hom-colimit` to Step 2/3 dependencies and verbatim citations, because essential-constancy transport and canonical uniqueness are not definition-only two-line facts.
