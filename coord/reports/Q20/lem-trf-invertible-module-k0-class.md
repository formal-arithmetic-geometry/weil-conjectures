## Files written

- `dag/nodes/sec-trace-formula/lem-trf-invertible-module-k0-class.json` — statement, four proof steps, and split metadata; no new nodes.
- `citations.json` — verbatim statement excerpts for every node used by every proof step.

## Attachments

None. No sorry-free declaration in the read-only slopmaster2 source states this item exactly.

## WANTED:

None.

## What was wrong or changed

The imported node had an empty proof and an unspecified proof origin. I filled the proof using the finite syzygies of the given exact finite free resolution, recorded Tag 0AFY as the source, and filled the blueprint place and split report. The mathematical statement itself is faithful to Tag 0AFY: the integer is the alternating sum of the finite free ranks. No new node was created because the only auxiliary facts are the exactness definition, the projective lifting/direct-summand equivalence, finite generation from a finite basis, and the defining K₀ relation; each is already stated by a cited node. The inherited `created` metadata names Q21's earlier import; it was retained as required for imported fields.

## What I could not finish

Nothing. The required Mathlib searches were run and logged for the item; they found no K₀/perfect-complex theorem. The server `check_dag` and `review_split` checks both passed.

## Review by Q20

I re-read the current item node, the `sk-i-curve-zero` unit, the `sec-trace-formula` chapter record, the Stacks source around Tag 0AFY in `literature/stacks-project/more-algebra.tex`, and every cited definition node. In this repair I specifically re-read the revised `def-trf-k0-group`: its statement now includes the explicit set of projective quotient representatives as well as the generator relation, and the K_0 citations below use that current statement verbatim. Step 1 uses the exact-sequence node only for the image-equals-kernel meaning of exactness, and I checked that the syzygies are introduced with the correct endpoints, including the leftmost isomorphism and the `d=0` case. Step 2 uses the projective-module node's lifting property to split each surjection onto a syzygy; its direct-summand clause gives projectivity of the kernels, while the finite-free basis and finite-generation definitions justify finite generation by projected basis elements. Step 3 uses the current K₀ definition's generator and direct-sum relation after the chosen splittings; the exact-sequence and projective hypotheses ensure all displayed classes are legitimate generators, and I checked that the revised explicit presentation still supplies this relation. Step 4 uses the same current K₀ relation and the free-module basis definition to identify each free term with a finite direct sum of copies of `S`, then performs the alternating cancellation; the citation quote was refreshed against the revised definition. I checked that every `uses` entry has a verbatim quote in `citations.json`, that `proof_deps` is the union of those uses, that no step cites a proof rather than a statement, and that no step hides a separate lemma or exceeds the long-step threshold. The source route and blueprint reference were updated to the finite-free-complex/K₀ argument, and the server DAG and split reviewers passed.
