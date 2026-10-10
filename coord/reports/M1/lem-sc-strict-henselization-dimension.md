# Stage-1 split: lem-sc-strict-henselization-dimension

## Files written

- `dag/nodes/sec-curve-estimates/lem-sc-strict-henselization-dimension.json`: item, split in two proof steps.
- `dag/nodes/sec-curve-estimates/lem-sc-faithfully-flat-local-dimension.json`: statement-only prerequisite, Stacks Algebra 112.1.
- `dag/nodes/sec-curve-estimates/lem-sc-etale-local-dimension.json`: statement-only prerequisite, Stacks 07QP.
- `dag/nodes/sec-curve-estimates/lem-sc-filtered-colimit-prime-chain-dimension.json`: statement-only prerequisite, the chain-contraction argument in Stacks 06LK.
- `citations.json`: verbatim statement quotes for every citation.

## Attachments

None. Grep of both WeilConjectures source trees for the item tag, strict henselization dimension terminology, and likely declaration names found no sorry-free declaration stating this item.

## Sources and route

I read the Stacks Project More on Algebra Tag 06LK (Lemma 45.7). Its proof first uses faithful flatness of $R\to R^{sh}$ and going down, then writes $R^{sh}$ as a filtered colimit of localizations of etale $R$-algebras, contracts any finite prime chain to one stage, and applies Tag 07QP (Lemma 44.2) to identify the dimension of each stage with $\dim R$. The item statement is unchanged. The three new nodes are strict prerequisites of those two arguments and are statement-only nodes.

## Not duplicates

- `lem-sc-faithfully-flat-local-dimension` vs `lem-pc-local-flat-faithful-flat-reflects-surjective`: the existing node proves faithful flatness from a local flat map; the new node uses faithful flatness to compare Krull dimensions.
- `lem-sc-etale-local-dimension` vs `lem-weil-pbc-strict-henselization-triples`: the existing node constructs the strict henselization colimit; the new node is the independent dimension theorem for one etale localization.
- `lem-sc-filtered-colimit-prime-chain-dimension` vs `lem-weil-pbc-strict-henselization-triples`: the existing node states filteredness and the colimit presentation; the new node gives the prime-chain contraction and dimension bound.
- `lem-sc-filtered-colimit-prime-chain-dimension` vs `lem-sc-strict-henselization-dimension`: the item asserts equality for a strict henselization; the new node is the general filtered-colimit upper-bound lemma used inside that equality proof.
- `lem-sc-strict-henselization-faithfully-flat-local` vs `lem-sc-strict-henselization-dimension`: the new node supplies the faithful-flat-local map used for the lower inequality, while the item concludes equality of Krull dimensions.
- `lem-sc-strict-henselization-faithfully-flat-local` vs `lem-sc-strict-henselization-dvr`: the existing DVR node is a scheme-stalk statement with a Noetherian hypothesis and only states flat-locality; the new node is the ring-theoretic faithful-flat-local property needed for arbitrary local rings.
- `lem-sc-strict-henselization-faithfully-flat-local` vs `lem-sc-strict-henselization-cotangent-dimension`: the cotangent node compares residue-field vector spaces under a Noetherian hypothesis and does not state flatness or locality.

## Review by M1

I checked the item against Tag 06LK and read the statement of every cited node. Step 1 uses the strict-henselization-triples statement for the filtered etale presentation and the new faithful-flat-local-dimension statement for exactly the inequality it asserts; the locality and faithful-flatness hypotheses are those of the canonical strict henselization map in the cited Stacks result. Step 2 uses the same triples statement for the stages, the new filtered-colimit chain statement for contraction of a finite chain, and the new etale-local-dimension statement for each stage. The equality of the supremum with $\dim R$ is then immediate because every stage has that dimension. The new statements were tested on a field (dimension zero), a DVR (dimension one), and a polynomial localization; no edge case contradicts them. Searches were run for all three new nodes with LeanFinder, Loogle, and Mathlib grep; no exact Mathlib declaration was found. The item itself was also searched; the only hits were unrelated Krull-dimension lemmas.

## What was wrong or incomplete

The imported item had no proof or dependencies despite citing Tag 06LK. I supplied the two source-faithful inequalities and made all non-elementary facts explicit as statement-only nodes. No source error was found.

## What remains

The four prerequisite nodes are intentionally unsplit and join the stage-1 queue.

## Second reading by M1

- Item statement: checked against More on Algebra Tag 06LK (Lemma 45.7), including the local-ring and strict-henselization hypotheses; agrees.
- Step 1: checked against Tag 06LK and the exact statements of the new faithfully-flat-local node and the dimension inequality node; the lower-bound hypotheses now match explicitly.
- Step 2: checked against Tag 06LK and the strict-henselization triples, filtered-colimit chain, and etale-local-dimension statements; the stages are written as $(B_i)_{q_i}$ so the etale dimension node applies with its stated primes.
- `lem-sc-faithfully-flat-local-dimension`: checked against Algebra Tag 112.1 and the local faithfully-flat hypotheses; statement is self-contained and tested on a field and a DVR.
- `lem-sc-etale-local-dimension`: checked against More on Algebra Tag 07QP (Lemma 44.2), including the prime-over-prime data; statement is self-contained and tested on an identity etale map and a field etale extension.
- `lem-sc-filtered-colimit-prime-chain-dimension`: checked against the chain-contraction paragraph of Tag 06LK; the finite-chain and supremum conclusion are explicit and tested on constant and localization-filtered diagrams.
- `lem-sc-strict-henselization-faithfully-flat-local`: checked against More on Algebra Tag 07QM and the first sentence of Tag 06LK; all ring-map notions have definition nodes and the statement is tested on the identity strict henselization of a separably closed field.

Changes: added the missing faithful-flat-local prerequisite and citation; rewrote the upper-bound step to name localized etale stages and the exact prime data; updated proof dependencies and citations. No Mathlib leaf was found for any new prerequisite.
