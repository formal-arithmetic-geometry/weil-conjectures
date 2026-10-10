1. Files written

- `dag/nodes/sec-abelian-varieties/lem-pqf-finite-spectrum-maximal-primes.json`: item split; no new nodes.
- `citations.json`: citation for step 1.

2. Attachments

None.

3. WANTED

None.

4. Problems found

The item was not stated by any declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`. A stronger downstream node, `pqf-lem-finite-type-algebra-finite-spectrum`, already uses this item, so citing that node would create a cycle. The existing Mathlib leaf `lem-weil-pbc-finite-type-over-field-prime-intersection-maximal` supplies exactly the Jacobson intersection statement needed for the finite-product argument. No statement or blueprint error was found.

5. Unfinished work

Nothing unfinished.

## Review by H1

I read the item source, Stacks `algebra.tex`, Lemma 0ALW, and checked the item statement clause by clause: a field, a finite-type commutative algebra (including the zero ring), finite prime spectrum, and maximality of every prime. I searched the project Lean source by the item tag and by the relevant phrases; no project declaration states it. I also read the complete statement of `lem-weil-pbc-finite-type-over-field-prime-intersection-maximal`, whose Jacobson conclusion is quoted verbatim in `citations.json` and is the only non-elementary input.

Step 1 uses that node to identify a prime with the intersection of the maximal ideals above it. Finiteness of `Spec B` makes this a finite intersection. If the prime were non-maximal, choosing an element outside it from each strictly larger maximal ideal gives a finite product in the intersection, while primality says one factor is in the prime, which is contradictory. The empty-family case is excluded because the cited intersection would be the whole ring; the zero ring has no primes, so it is vacuous. These checks cover the hypotheses at the only step and the small zero-ring edge case. I searched the blueprint for duplicate statements and found none; no new node was created.
## Second reading by H1

- Source statement: checked against Stacks `algebra.tex`, Lemma 0ALW (`lemma-finite-type-algebra-finite-nr-primes`), especially the implication from finitely many primes to dimension zero; the field, finite-type, and finite-spectrum hypotheses agree. The zero-ring extension is vacuous because its spectrum is empty.
- Step 1: checked against the complete statement of `lem-weil-pbc-finite-type-over-field-prime-intersection-maximal`; it supplies exactly the Jacobson intersection. The finite-product and primality argument is explicit, and the nonempty-family and zero-ring cases were checked.
- New nodes: none; B1--B7 and duplicate-node checks are vacuous. The existing Jacobson node was searched and cited instead of creating a duplicate.
- Small cases: for the zero ring the conclusion is vacuous; for a field the sole prime is maximal; for a nonzero finite-type algebra the source's nonzero hypothesis applies directly.

Changes made in this second reading: added this source-by-label, dependency, edge-case, and no-new-node audit. No mathematical statement or proof step required repair.
