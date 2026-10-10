# Stage 1 report: def-weil-pbc-constructible-torsion

Files written:

- `dag/nodes/sec-proper-base-change/def-weil-pbc-constructible-torsion.json` — definition, split; no new nodes and no Mathlib leaves.
- `citations.json` — verbatim statement excerpts for every proof-step citation.

Attachments: none. No declaration in `WeilConjectures/` carries the blueprint tag `(blueprint: def-weil-pbc-constructible-torsion)`, and no sorry-free declaration was found that states this specialized definition exactly.

WANTED: the imported blueprint source file `literature/blueprint/master/blueprint/sec-proper-base-change/sk-curve-calculations-pbc-for-the-projective-line--remark-1/def-weil-pbc-constructible-torsion.md` is not present in this checkout; the split was checked against the node statement and Stacks sources instead.

The imported node had no proof steps or explicit dependencies for the stratification, constructible-stratum, inverse-image, and finite-locally-constant notions. I retained its statement and added those existing DAG definitions as statement dependencies. The definition is a specialization of the general constructible abelian-sheaf notion, but I did not create a duplicate node because the target's curve-coefficient hypotheses are part of this item's statement.

## Review by M1

I read the target node, the curve coefficient pair definition, and the existing definitions of stratification, constructible subset, inverse image, and finite locally constant sheaf. I checked the target sentence against Stacks Definition 03RW(2), Definition 03RU, and Lemma 095E(3): the curve pair supplies the scheme and torsion abelian sheaf; the remaining clause is exactly a finite partition by locally closed constructible subschemes with finite locally constant restrictions. Step 1 cites the stratification statement for the finite partition and the constructible-subset statement for each stratum. Step 2 cites the inverse-image definition for the restriction along an immersed stratum. Step 3 cites the finite-locally-constant definition, whose statement is precisely locally constant plus finite stalks. Each citation quote in `citations.json` is copied verbatim from its node. I tested the edge cases conceptually: the empty curve has the empty finite partition, and a one-stratum constant finite sheaf satisfies the definition. Mathlib searches were run for the item by LeanFinder, Loogle, grep, and LeanSearch; only unrelated quasi-compact scheme lemmas appeared, while LeanSearch was unavailable.

What could not be finished: the blueprint markdown source is absent from this checkout, so its exact prose was unavailable; no new mathematical node was required.

## Second reading by M1

- Item statement: checked against Stacks Definition 59.71.1 (Tag 03RW, labelled `definition-etale-constructible`) and the Noetherian reformulation in Section 59.74 (Tag 03RY); the original wording omitted the explicit immersion data and did not identify the restriction as inverse image.
- Proof steps: none; this is a statement-only definition node, so the former `citations.json` entries were not proof dependencies and were not used as steps.
- New nodes: none; existing definitions were searched in `dag/nodes/` and used as statement dependencies only.
- Hypotheses and edge cases: the curve coefficient pair supplies a finite-type-over-a-field (hence Noetherian) curve and torsion abelian sheaf; the empty curve is covered by the empty finite family, and a one-stratum constant finite sheaf satisfies the definition. The field and zero-sheaf cases impose no extra conditions.
- Source location: the checkout lacks the imported blueprint markdown and Stacks `.tex` tree, so the source field now records the Stacks tag and label verified from the public Tag 03RW/03RY pages.
- Changed the statement to quantify immersions with pairwise disjoint locally closed constructible images covering $C$, and to write each stratum restriction as $\iota_i^{-1}F$.
- Added statement dependencies for locally closed subsets, constructible subsets, inverse image, and finite locally constant sheaves; set the blueprint `from`/`same_as` fields required for this item.
- Cleared the stale proof-citation interpretation: the node has no proof steps and no new nodes.
