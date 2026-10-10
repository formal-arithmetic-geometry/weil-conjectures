# pqf-lem-finite-qf

1. Files written:
   - `dag/nodes/sec-abelian-varieties/pqf-lem-finite-qf.json`: item recorded as a Mathlib leaf, matched exactly by `AlgebraicGeometry.instLocallyQuasiFiniteOfIsFinite`.
   - `citations.json`: empty, because the item has no natural-language proof steps after the Mathlib match.
2. Attachments: none.
3. WANTED: none.
4. The imported item is exactly the standard assertion that a finite morphism of schemes is quasi-finite. Its imported proof was not retained as a split proof because Mathlib supplies the assertion directly.
5. Nothing remains unfinished.

## Review by H1

I read the item source `literature/blueprint/master/blueprint/sec-abelian-varieties/sk-prop-av-pqf-finite/pqf-lem-finite-qf.md` and verified that its statement is precisely “A finite morphism of schemes is quasi-finite.” I checked the Mathlib source `Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean` at line 90: the instance `AlgebraicGeometry.instLocallyQuasiFiniteOfIsFinite` has hypothesis `[IsFinite f]` and conclusion `LocallyQuasiFinite f`, with a docstring stating the same claim. The LeanFinder search returned that declaration as its top match; the grep search independently found the line. Loogle returned no result because the unqualified query produced an unknown-identifier response, and LeanSearch was unavailable; both results are recorded verbatim in `mathlib_searches`. No proof-step citations or new nodes are needed for an exact Mathlib leaf, and `blueprint.same_as` is the empty list after searching the blueprint.

## Source error

The Mathlib instance `AlgebraicGeometry.instLocallyQuasiFiniteOfIsFinite` only concludes Mathlib's `LocallyQuasiFinite`; the project's `pqf-def-quasifinite` additionally requires finite type and finite fibres. Therefore the worker's claimed exact leaf was too weak and was replaced by the explicit project-level argument.

## Second reading by H1

- Item statement: checked against the blueprint node (order 530) and Stacks Morphisms Lemma 29.21.10, Tag 02NH; finite morphism implies project quasi-finite, with hypotheses retained.
- Step 1: checked that the scheme conventions supply finite type and quasi-compactness, `pqf-lem-finite-fibres` supplies finite fibres, and `pqf-lem-qf-finitefibres` supplies the reverse implication; verdict: complete and non-circular.
- Existing node `lem-weil-pbc-finite-closed-map-finite-fibres`: checked directly; its clause (2) states the finite-fibre fact needed here, so no duplicate node is retained.
- Small cases checked: the empty scheme, a field identity morphism, and a finite disjoint union of points all have finite fibres and satisfy the conclusion.
- Changed the item from the overly strong Mathlib leaf to one explicit proof step; reused the existing finite-fibre node, added its verbatim citation quote, and filled blueprint provenance for the item.

## Not duplicates

`pqf-lem-finite-qf` uses `lem-weil-pbc-finite-closed-map-finite-fibres` because that existing node's clause (2) states finite fibres for finite morphisms; the discarded draft `pqf-lem-finite-fibres` was an exact duplicate and was removed.
