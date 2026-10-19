Files written:

- `dag/nodes/sec-trace-formula/lem-trf-local-map-completion-approximation.json` — repaired statement split, six proof steps, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-artin-approximation-etale-local-map.json` — repaired statement-only Tag 0CAR child, no Mathlib match.
- `citations.json` — verbatim statement quotes for every cited node in every proof step.

Attachments: none. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its blueprint tag, and its main notions; no sorry-free project declaration states the item exactly.

WANTED: none; the local Stacks sources contain Tags 0CAU, 0CAR, and 07PV.

What was wrong in the returned delivery and what changed: the return identified C1/C2/C4 and E1/E3/E4 faults in Steps 1–3. The old proof conflated the base ring `R` with the coordinate ring `A`, asserted the wrong G-ring hypothesis, and applied 0CAR to `R` although its hypotheses are about the ring whose localization is G. I now localize the base at `r=p∩R`, use the Tag 07PV finite-type transfer to make `A_p` a G-ring, and apply the child to `A`, `p`, and the images of the equations in `A[x]`. The old Step 3 only showed `q ⊆ phi⁻¹(p')`; the repaired split proves both inclusions using the injective residue-field map induced by the given local map, so the localization `B_q → A'_{p'}` is genuinely local. The denominator calculation is written explicitly rather than hidden under “clear denominators”. The child statement was corrected from an `R`-based version to the exact 0CAR statement with `A_p` G-ring. The existing cross-unit node `lem-weil-pbc-finite-type-over-g-ring` was searched and read and is cited for the 07PV transfer; it is a generic tool because this unit has no separate G-ring ascent node.

## Not duplicates

- `lem-trf-artin-approximation-etale-local-map` vs `lem-weil-pbc-henselian-approximation-alg-hom`: the new node approximates polynomial solutions in a local completion by solutions after an étale ring extension with a chosen prime and unchanged residue field; the existing node concerns a henselian pair and an exact map into the base ring modulo the defining ideal, with no étale extension.
- `lem-trf-artin-approximation-etale-local-map` vs `lem-weil-pbc-finite-type-over-g-ring-formal-fibres`: the new node is an Artin approximation/existence statement for polynomial solutions; the existing node asserts regularity of completion maps for finite type algebras over G-rings.
- `lem-trf-artin-approximation-etale-local-map` vs `lem-weil-pbc-henselian-pair-approximation`: the new node produces an étale algebra and residue-field-preserving prime; the existing node is the henselian-pair approximation property for solutions in the original ring.
- `lem-trf-artin-approximation-etale-local-map` vs `lem-trf-local-map-completion-approximation`: the child is the affine polynomial Artin-approximation input (Tag 0CAR), while the item is the geometric local-map approximation theorem (Tag 0CAU) that applies this input and constructs an étale neighbourhood; neither is a restatement of the other.
- `lem-trf-artin-approximation-etale-local-map` vs `def-weil-pbc-associated-graded-ring`: the child is an existence theorem for étale approximation of polynomial solutions; the existing node is only the definition of an associated graded ring (Tag 07XA), with no approximation assertion.
- `lem-trf-artin-approximation-etale-local-map` vs `lem-weil-pbc-associated-graded-ring-structure`: the child is an étale Artin approximation theorem; the existing node proves structural facts about the associated graded ring (Tag 07XA), and does not state or imply approximation of solutions.

## Review by Q13

I read the returned item and child, the unit `sk-i-curve-zero`, the chapter record, the current blueprint ancestry, and the full source proofs of Stacks Tag 0CAU (`literature/stacks-project/more-morphisms.tex`, lines 11017–11068), Tag 0CAR (`literature/stacks-project/smoothing.tex`, the lemma at lines 3347–3370), and the G-ring transfer Tag 07PV. I also opened the statements of every cited definition and of `lem-weil-pbc-finite-type-over-g-ring`; the latter says that a finite-type algebra over a G-ring is a G-ring, exactly the transfer used in Step 1.

Step 1 now introduces distinct rings `R`, `A`, and `B`, localizes at `r=p∩R`, verifies that `R=O_{S,s}` is the assumed G-ring, and cites the finite-type transfer before invoking the 07PV localization clause for `A_p`. Step 2 cites the repaired child verbatim and checks every child hypothesis: `A` is Noetherian, `p` is prime, the equations have coefficients in `A`, the completed tuple is a solution, `A_p` is G, and `N≥1`. Step 3 uses only the child’s etale map, prime, residue-field isomorphism, and approximating tuple; its polynomial congruence is expanded from the generator congruences. Step 4 uses the local residue-field map and the same congruence to prove both inclusions in `phi⁻¹(p')=q`, repairing the precise locality gap identified by the return. Step 5 cites the child and completion definition while writing the fraction identity and checking that denominators outside `q` become units, so the congruence extends from polynomials to all of `B_q`. Step 6 cites the étale, residue-field, and completion definitions to translate the affine construction back to the schemes and identify `p'^N` with `m_u^N`.

I regenerated `citations.json` from the current node statements, so each quote is verbatim and every `uses` entry is covered. I reran all four required Mathlib search kinds for the repaired child and item; the logs record the actual hits and no-match verdicts. I checked the edge cases `N=1`, a field local ring (zero maximal ideal), the identity local map, and a presentation with no relations. No new definition or duplicate node was introduced; the only new node remains the strict Tag 0CAR affine input.

What could not be finished: no Lean work, compiler, Lake, or build was run, as required for stage 1.
