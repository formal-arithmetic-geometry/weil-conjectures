Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-picard-locus-closed-valuation-triviality.json` — split Tag 0EX8 proof.
- `dag/nodes/sec-abelian-varieties/lem-sc-valuation-fp-torsionfree-free.json` — statement-only child; Mathlib generalizations only.
- `dag/nodes/sec-abelian-varieties/lem-sc-valuation-zero-section-relative-cartier.json` — statement-only child; no Mathlib exact match.
- `dag/nodes/sec-abelian-varieties/lem-sc-valuation-proper-coherent-sections.json` — statement-only child; no Mathlib exact match.
- `citations.json` — verbatim quotes for every non-elementary citation.

Attachments: none.

WANTED: none.

What was wrong: the imported item had no proof and was the missing non-elementary input to the parent Tag 0BF0 split. The Stacks proof has separate DVR and general valuation-ring arguments, so I represented both and added the missing coherent-sections, finite-free, and relative-Cartier statements. No existing DAG node states these combined facts.

What could not be finished: no Lean declaration exists for Tag 0EX8, and the stage-1 contract forbids writing Lean.

## Not duplicates

lem-sc-valuation-fp-torsionfree-free vs lem-sc-dvr-fg-torsionfree-free: the existing node is only for discrete valuation rings and finitely generated modules; this node is for arbitrary valuation rings and finitely presented modules.
lem-sc-valuation-proper-coherent-sections vs lem-pc-coherent-hi: the existing node assumes a locally Noetherian base; this node covers coherent valuation rings, which need not be Noetherian.
lem-sc-valuation-zero-section-relative-cartier vs lem-pc-recd-locally-principal: the existing node requires all fibre zero schemes to be effective Cartier divisors; this node packages the valuation-ring integral closed-fibre specialization used in Tag 0EX8.
lem-sc-valuation-fp-torsionfree-free vs lem-sc-picard-locus-closed-valuation-triviality: the existing item concludes triviality of an invertible sheaf on a proper scheme from generic triviality; this child is the independent algebra lemma that a finitely presented torsion-free module over any valuation ring is finite free.
lem-sc-valuation-proper-coherent-sections vs lem-sc-picard-locus-closed-valuation-triviality: the existing item concludes line-bundle triviality; this child is the cohomological finiteness input that global sections are finitely presented over the valuation ring.
lem-sc-valuation-zero-section-relative-cartier vs lem-sc-picard-locus-closed-valuation-triviality: the existing item concludes the line bundle is trivial; this child only asserts that a section nonzero on the integral closed fibre has a relative effective Cartier zero scheme.

## Review by J1

I read the complete proof of More on Morphisms Lemma `lemma-triviality-generic-fibre-valuation-ring` (Tag 0EX8), including its DVR reduction and its general valuation-ring argument. Step 1 follows the DVR paragraph and cites the existing finite torsion-free DVR freeness statement. Step 2 follows the coherence, torsion-free, finite-free, and flat-base-change paragraphs; the three new and existing statements supply precisely those claims. Step 3 records the nonvanishing-on-the-closed-fibre argument and cites the new relative-Cartier zero-locus statement. Step 4 is the final properness, fibre-Cartier, and generic-fibre contradiction argument, written as an elementary consequence of the preceding construction. I checked all child statements against the source wording, searched the whole DAG and blueprint for duplicates, ran LeanFinder, Loogle, grep, and LeanSearch for each new node and the item, and recorded the exact results. Small cases checked include a field valuation ring, a DVR, and rank-one free global sections.

## Second reading by J1

- Item statement: checked against More on Morphisms Lemma `lemma-triviality-generic-fibre-valuation-ring`, Tag 0EX8; verdict: agrees after making `f`, the generic fibre, and the integral closed fibre explicit.
- Step 1: checked against the DVR paragraph of Tag 0EX8 and `[lem-sc-dvr-fg-torsionfree-free]`; verdict: cited statement supplies finite freeness and the remaining divisor argument is written in the step.
- Step 2: checked against the coherent-cohomology, generalized valuation-module, and flat-base-change paragraphs of Tag 0EX8; verdict: cited statements supply finite presentation, finite freeness, and base change under the stated proper flat finite-presentation hypotheses.
- Step 3: checked against the filtered-colimit and fibre-Cartier paragraphs of Tag 0EX8; verdict: the nonvanishing argument is stated and the relative-Cartier citation matches verbatim.
- Step 4: checked against the final properness and fibre-Cartier paragraph of Tag 0EX8; verdict: elementary deduction from relative Cartier flatness and empty generic zero locus.
- `lem-sc-valuation-fp-torsionfree-free`: checked against Tag 0EX8's generalized valuation-ring module input and DAG/Mathlib searches; verdict: self-contained statement-only auxiliary, no exact Mathlib declaration.
- `lem-sc-valuation-proper-coherent-sections`: checked against Tag 0EX8's coherent-ring/cohomology paragraph and DAG/Mathlib searches; verdict: self-contained statement-only auxiliary, no exact Mathlib declaration.
- `lem-sc-valuation-zero-section-relative-cartier`: checked against Tag 0EX8's fibre-Cartier application and definitions of zero scheme and relative effective Cartier divisor; verdict: repaired to include properness, which is required by the source argument.

Changes made: repaired JSON TeX escaping in the relative-Cartier child and its citation; added the missing properness hypothesis and all definition dependencies to that child; made the item morphism, generic fibre, and integral closed fibre explicit and added its integral-scheme dependency. Dry-run preflight passed after these repairs.
