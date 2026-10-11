Files written:
- `dag/nodes/sec-picard-framework/lem-pc-ring-pseudo-coherent-iff-all-m.json`: statement split, no new nodes, Mathlib no match.
- `citations.json`: verbatim citations for the two non-elementary uses.

Attachments: none.

WANTED: none.

What was wrong in the node or blueprint: the item was unsplit and had no proof. The source is Tag 064U; the imported statement already matches its ring-level finite-free formulation. No supporting node was needed because the DAG already contains the precise distinguished-triangle closure and finite-cohomology statements.

## Review by G1

I read the target node, its ancestor blueprint reference to the m-pseudo-coherence induction, the existing ring triangle node `lem-pc-ring-pseudo-coherent-distinguished-triangle`, and `lem-sc-finite-cohomology`. I also checked the source place More on Algebra, Lemma 15.66.5, Tag 064U. Step 1 uses only the definition and stupid truncation of a bounded-above finite-free model, so it is marked elementary. Step 2 follows the source's descending construction: the cone long exact sequence supplies vanishing, the triangle node supplies (n-1)-pseudo-coherence, and the finite-cohomology node supplies finite generation of the obstruction group; the citations quote exactly the statements used. The hypotheses match at each use: the cone is (n-1)-pseudo-coherent and vanishes above n-1, while the truncated finite-free complex is (n-1)-pseudo-coherent. I tested the zero complex and the case m above the upper bound; both directions reduce to the zero witness or a finite truncation. Mathlib searches were rerun with the exact item statement: LeanFinder and grep found no pseudo-coherence declaration, Loogle returned no `PseudoCoherent` identifier, and LeanSearch was unavailable.

What could not be finished: no Lean implementation was required or written at this stage.

## Second reading by G1

- Item statement: checked against More on Algebra, Lemma 15.66.5, Tag 064U, including the ring, derived-category, bounded finite-free, and all-integer hypotheses; verdict: agrees hypothesis by hypothesis.
- Step 1: checked against the (1) implies (2) proof of Tag 064U; stupid truncation of a bounded-above finite-free model supplies the stated bounded witness and the claimed cohomology maps; verdict: elementary and correct.
- Step 2: checked against the (2) implies (1) proof of Tag 064U and the long-exact-sequence induction there; the cited triangle node supplies the cone's (n-1)-pseudo-coherence and the finite-cohomology node supplies finite generation of its top obstruction; verdict: dependencies state exactly what is used, and the remaining finite-free choice and cone lift are elementary module and complex constructions.
- Existing node `lem-pc-ring-pseudo-coherent-distinguished-triangle`: opened and checked against Tag 064R; its first clause applies with the truncated finite-free complex as A and C as B, under the stated degree bounds; verdict: exact supporting statement, not a duplicate new node.
- Existing node `lem-sc-finite-cohomology`: opened and checked against Tag 064S; its vanishing hypothesis matches the cone's H^i = 0 for i >= n after setting m = n-1; verdict: exact supporting statement, not a duplicate new node.
- New nodes: none; therefore B1-B7 and duplicate/Mathlib-leaf checks introduce no additional node obligations. The recorded Mathlib searches were inspected and their unavailable LeanSearch result is correctly marked unavailable.
- Edge cases: zero complex and m above the cohomological upper bound reduce to the zero witness/truncation; a field ring satisfies the same construction; no hypothesis changes occur for n = 0 or n = 1.

Changes made: corrected the node's stale `created.item` metadata from `lem-pc-ring-pseudo-coherent-localization-glue` to this item, so delivery ownership is accurate. No mathematical statements or proof steps required alteration.
