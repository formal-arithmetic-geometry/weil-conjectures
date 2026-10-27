## What changed

Proved `AlgebraicGeometry.ProjectiveSpace.exists_standardUnitCocycle_normalization_of_pairwise_laurent`
in `Sheaf.AlgebraicGeometry.ProjectiveSpace.PairwiseCocycleNormalization`, preserving its statement
and existing public imports. Added a private proof import of
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineDifferentials`, which also exposes the
already proved monomial basis in `TwistSections`. All new helpers are private and fully proved.

The proof restricts to the open where all coordinates are invertible, computes the restrictions
of the transition units as degree-zero Laurent monomials, and compares their unique coefficients.
The triple equalities imply a single exponent. Explicit scalar chart units, based at chart zero,
then give the required equality on the original pairwise overlaps. Both orientations and pairs
involving the base chart are handled explicitly. The argument includes zero and negative exponents,
all field characteristics and the smallest allowed coordinate count, three.

Updated the item's DAG proof, proof dependencies and proof origin to describe this implementation.
No other existing module or node changes. A theorem-local unused-variable linter setting preserves
the existing named nondependent function binders in the public statement.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProjectiveSpace.exists_standardUnitCocycle_normalization_of_pairwise_laurent`
(node `new-sfb-projective-pairwise-cocycle-normalization`).

Item holes: 1 before, 0 after. Added holes: 0. Split-off statements: 0.
The final `lcompile.py` check passes without warnings in 9.7 seconds.
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound` for the
completed theorem. The public statement was also checked byte-for-byte against the original;
no signature text changed.

The proof does not invoke any theorem containing `sorry`, including the pairwise Laurent-unit
existence theorem. The constants it uses from that module are actual ring maps and unit maps.

## No longer needed

No imports or modules withdrawn. The existing public imports remain necessary for the statement,
including `standardOpenConstUnit` from `PairwiseLaurentUnitExpansion`.
The theorem `exists_pairwise_laurent_unit_expansion` is not used in this proof: its expansion is
already an explicit hypothesis. Its node and module remain needed by the parent off-diagonal
normalization theorem and by the constant-unit definitions, so they are not pruned.

No separate existence theorem for chart scalars or connectivity theorem for the pair graph is
needed: the proof constructs the scalars and proves the elementary index comparisons directly.

## Where the brief, the DAG or earlier work was wrong

The original plan correctly identifies the mathematical comparison, but did not point to the
already proved general monomial-basis theorem `ProjectiveSpace.bijective_sum_awayMonomial` or
the multiplication API in `LineDifferentials`. Those suffice to close this obligation completely.
Using the full coordinate torus avoids developing separate triple-overlap Laurent coordinate
isomorphisms. The unit route and public statement are preserved.

The current server queue was checked: this is a one-hole proof item, not a zero-hole repair;
there was no current build-error file or rework row for it.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProjectiveSpace.PairwiseCocycleNormalization": "d08562a899b87affb4f20f8f56b38eaf1fb64a75"}, "results": {"Sheaf.AlgebraicGeometry.ProjectiveSpace.StandardUnitCocycleOffDiagonal": {"hash": "0a3a642571bf32e42e2b4bd9a0023f641e5e0db2", "status": "OK"}}, "seconds": 67, "time": "2026-10-28T04:08:49+0800", "transitive": 0, "version": 1}
```

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
