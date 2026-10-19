# Stage 1 report: lem-trf-oriented-constructible-coherent

Files written:

- `lem-trf-oriented-constructible-coherent.json`: statement split, one new set-valued criterion cited.
- `lem-trf-coherent-set-criterion.json`: statement-only unsplit child; Mathlib verdict no match.
- `citations.json`: verbatim statement quotes for every step citation.

Attachments: none. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the upstream reference for the item tag and for the oriented constructibility/coherence terminology; no sorry-free declaration states this item exactly.

WANTED: Orgogozo, “Modifications et cycles proches sur une base générale”, author draft §8.1 (printed pp. 17–18), for the coherence criterion and finite-module specialization. The URL is recorded in both node source fields, but no local archival copy is present in `literature/`.

What I checked and corrected:

- The imported item statement is unchanged. Its hypotheses are exactly a locally Noetherian, quasi-compact base, a finite-presentation morphism, a finite commutative coefficient ring, and a module sheaf on the vanishing topos.
- The new child is the set-valued criterion, which is strictly more general in coefficients than the item and is not a restatement of a module clause. I searched the whole DAG and both blueprint snapshots for this criterion and found no duplicate.
- The item’s first step applies that child to the underlying sheaf of sets. The second step uses the existing definition [def-trf-oriented-constructible-sheaf]: its finite module values are finite sets, so forgetting operations gives the set-valued witnesses required by the child. The third step uses the converse of the child and transports the existing \\Lambda-module operations across each finite constant-set trivialization; naturality makes the transition maps \\Lambda-linear, giving exactly the module-valued witnesses in the definition.
- I read the complete statements of [def-trf-oriented-constructible-sheaf], [def-trf-oriented-nearby-cycles], and [def-trf-coherent-topos] before writing the proof. The step citations in `citations.json` quote the exact sentences used. The finite-module upgrade is a local operation-transport argument, not an additional hidden geometric theorem.
- Edge cases checked in the statement: empty source or base gives the degenerate topos and empty stratifications; the zero module is locally constant with finite value; an infinite constant set is excluded by coherence/finite-value requirements; no connectedness or separatedness hypothesis was added.
- Mathlib searches were run for the new node with both phrasings using LeanFinder, Loogle, grep, and LeanSearch. Hits concerned generic coherent-site sheaf conditions, condensed objects, or ordinary constructible subsets; none states the oriented-product criterion. The exact queries and verdicts are recorded in the node’s `mathlib_searches`.
- No long proof step hides a separate lemma beyond the new set-valued criterion; the module-structure transport is the direct two-line local argument from the definition.

## Not duplicates

- `lem-trf-coherent-set-criterion` vs `lem-trf-oriented-constructible-coherent`: the child treats arbitrary sheaves of sets and is coefficient-independent; the item treats finite \\Lambda-module sheaves and additionally proves transport of module operations.
- `lem-trf-coherent-set-criterion` vs `def-trf-oriented-constructible-sheaf`: the existing node is only a definition of module constructibility, while the child is the non-elementary equivalence with coherence for set-valued sheaves.
- `lem-trf-coherent-set-criterion` vs `lem-trf-coherent-conservative-reflection`: the existing reflection node concerns a coherent conservative geometric morphism; the child concerns the finite-stratification criterion on one vanishing topos.

## Review by Q70

I read the imported item and its source metadata, then read the complete statements of each cited dependency. For step 1, the new child supplies exactly the equivalence for the underlying sheaf (A=|F|) under the item’s Noetherian and finite-presentation hypotheses. For step 2, the constructibility definition supplies finite stratifications and locally constant finite \\Lambda-module restrictions; forgetting the operations gives finite-set restrictions, so the child’s forward implication applies. For step 3, the child supplies finite-set trivializations; the module operations on (F) transport across each trivialization and commute with restriction maps by sheaf naturality, so the resulting constant values are finite \\Lambda-modules. I checked that no step assumes a cited node says more than its statement, and that `proof_deps` is exactly the union of the step uses. I also checked the empty and zero cases and verified that no extra geometric or coefficient hypotheses entered the split.

