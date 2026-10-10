# Stage-1 split: lem-sc-integral-overring-jacobson-power

## Files written

- `dag/nodes/sec-curve-estimates/lem-sc-integral-overring-jacobson-power.json`: split the existing statement into four proof steps; no new nodes or Mathlib leaves.
- `citations.json`: exact statement quotes for every cited node in the four steps.

## Attachments

None. A search of `WeilConjectures/` in the read-only slopmaster2 checkout found no project declaration stating this item.

## Sources and changes

I read Stacks Varieties Lemma 09N2, label `lemma-semi-local-dimension-one-conductor`, in `/home/ubuntu/c1-stacks-review/varieties.tex` lines 7417-7445; the repository's regenerated `literature/stacks-project/varieties.tex` is absent on this machine. The item's source is the paragraph beginning “Moreover, Spec(B') to Spec(A) is surjective.” The item already restricts the final assertion to `x` in `A`, as required. I kept its statement and blueprint reference. The imported item had no proof and no proof dependencies. I searched the whole DAG by 09N2, integrality, maximal ideals, and Jacobson radical, and the whole imported blueprint using `blueprint_refs.py search` for Jacobson radical, 09N2, and integral. Existing nodes cover all non-elementary inputs, so I created none.

The item-level Mathlib search was run with `msearch.py`: LeanFinder found the integral maximal-ideal theorems, grep found the relevant Mathlib declarations, Loogle's first query returned an unknown identifier, and LeanSearch was unavailable (HTTP 500). Those hits concern ingredients, not a direct statement of the item; the recorded searches in the existing node predate this split and were left untouched.

## Review by F1

I checked the item against the 09N2 paragraph and checked each cited node's full statement. Step 1 uses the monic-polynomial definition in `def-weil-pbc-integral-closure`; integrality over `A` follows from the same monic equation over `B`. Step 2 uses `lem-weil-pbc-integral-prime-over-maximal-maximal` for the prime supplied by the assumed surjective spectrum map and the explicit maximal-contraction clause of `lem-weil-pbc-integral-algebra-ideal-in-radical` for the converse; finiteness follows from semilocality of `B'`. Step 3 uses the ideal-extension clause of the latter node for `m_B A` and the former node after showing that a prime over `m_B A` contracts to a maximal ideal of `B`. The last point is the finite-product argument written in the step; this fills the equality that 09N2 states without proof. Step 4 uses the maximal-ideal correspondence already established in step 2, then the equality of step 3 and the definition of radical. The extra citation there names the exact prime-over-maximal fact used in that correspondence.

The hypotheses are in force: `B'` integral over `B` implies both intermediate integral extensions (step 1); the spectrum map is assumed surjective (step 2); `B'` and `B` are semilocal where their finite sets of maximal ideals are used (steps 2 and 3). In the edge case `B` is the zero ring, the empty intersection of maximal ideals is the unit ideal, handled explicitly in step 3. For a field `B`, `m_B=0`; every prime of the integral `A` contracts to zero and is maximal, so the equality reduces to `J(A)=sqrt(0)`, including finite products of fields. For `B` a DVR and `A=B`, the equality is immediate. I corrected the missing argument for the radical equality and used the existing Mathlib-leaf nodes instead of creating duplicates. No mathematical error in the item's statement or the blueprint passage was found.

## Unfinished

None. The source file must be regenerated from `literature/LIST.md` in the maintainer's checkout for independent source review; this sandbox contains no copy of it, as required.

## Second reading by F1

- Item statement: checked against Varieties Lemma 09N2, label `lemma-semi-local-dimension-one-conductor`, and its proof paragraph from “Moreover, `Spec(B') -> Spec(A)` is surjective”; the stated semilocal-overring hypotheses and the restriction `x in A` are coherent with the extracted argument.
- Step 1: checked against the integral-element definition node and the intermediate-ring inclusions; the monic equation over `B` is also one over `A`, and the step is elementary.
- Step 2: checked against the two cited integral-extension maximal-ideal statements; they give both directions of the maximal-ideal correspondence, and semilocality of `B'` gives finiteness.
- Step 3: checked against the cited ideal-in-radical and prime-over-maximal statements; the finite-intersection/product argument supplies the reverse radical inclusion, including the zero-ring (`t = 0`) case.
- Step 4: checked against the maximal-ideal correspondence from step 2 and the radical definition; the power conclusion is elementary once the equality from step 3 is established.
- New nodes: none; no duplicate or unnecessary supporting node was introduced.
- Citations: every non-elementary external fact in steps 1–3 has an exact statement quote in `citations.json`; no citation relies on a tag alone.
- Edge cases: checked the zero ring, a field, and `A = B` for a DVR; the conclusions remain meaningful and the explicit empty-intersection branch handles the zero ring.

Changes made: corrected the node's `created.item` metadata to this delivered item so preflight accepts it; no mathematical statements or proof steps required repair.
