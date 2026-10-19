## What changed

Completed `CategoryTheory.adjointMate` in
`lean/Sheaf/CategoryTheory/AdjointMate.lean`, following all four steps of
`lem-trf-adjoint-mate`. The witness is Mathlib's `conjugateIsoEquiv adj₁ adj₂ α.symm`.
Its component formulas are `conjugateEquiv_apply_app`; `unit_conjugateEquiv` gives
both unit compatibilities after cancellation of the mapped isomorphism.
Naturality of `α` and `conjugateEquiv_counit` give both counit compatibilities.
For uniqueness, cancel the mapped `α` in the two unit identities, then use
naturality at `adj₁.counit` and the right triangle identity to recover every
component. Only the existing theorem proof changed; signatures, definitions,
imports and the DAG route are unchanged.

Searches: LeanFinder found `Adjunction.rightAdjointUniq` and the induced
right-adjoint isomorphism API. Loogle found `conjugateEquiv_counit`. The grep
wrapper and direct source searches found `conjugateIsoEquiv`,
`unit_conjugateEquiv`, and the conjugation API in Mathlib's `Adjunction.Mates`.
Read the declared dependency `def-weil-pbc-adjunction-conjugate` and its
Mathlib realization; that is precisely the dependency used by the proof.

## Proved and sorry left

Closed 1 of 1 original holes: `CategoryTheory.adjointMate`
(node `lem-trf-adjoint-mate`). Added 0 holes, split off 0 statements.
No `sorry` remains in the delivered module. The proof uses only proved
Mathlib adjunction calculus and elementary categorical identities.

## No longer needed

None. No imports, nodes or modules were pruned. The declared dependency
`def-weil-pbc-adjunction-conjugate` remains necessary and is used through
`Mathlib.CategoryTheory.Adjunction.Mates`. The triangulated imports remain
necessary to state the unchanged hypotheses.

## Where the brief, the DAG or earlier work was wrong

None. The existing plan and component formulas are correct. Uniqueness needs
only the unit compatibility, exactly as the DAG's fourth step explains;
the counit compatibility hypothesis remains in the unchanged statement.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
