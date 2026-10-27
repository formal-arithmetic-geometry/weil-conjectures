## What changed

Proved `CategoryTheory.Adjunction.right_adjoint_additive_linear` in
`Sheaf.CategoryTheory.LinearRightAdjoint` by pairing
`adj.right_adjoint_additive` (Mathlib) and `adj.right_adjoint_linear`
(the adopted source library). Added their two modules as private proof imports:
`Mathlib.CategoryTheory.Adjunction.Additive` and
`WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor`.
The statement, public imports, definitions and docstrings are unchanged.

The two existing proofs implement exactly the DAG's inverse-Hom/counit
calculations: injectivity and distributivity prove additivity, and injectivity
and bilinear composition prove scalar compatibility. Thus the existing node
`lem-sbc-linear-right-adjoint`, its proof dependencies (the two linearity
definitions), and its unit route remain accurate and unchanged. The source
lemma's `Semiring` hypothesis specializes to the existing `CommRing` hypothesis.
No new result or auxiliary statement is required.

Compiled successfully using `lcompile.py` (4.0 seconds). A temporary
`#print axioms CategoryTheory.Adjunction.right_adjoint_additive_linear` reported
only `propext`, `Classical.choice` and `Quot.sound`; the diagnostic was removed
from the delivered file. The proof is uniform over the existing independent
universes and covers zero rings and empty categories without additional
hypotheses.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.Adjunction.right_adjoint_additive_linear`
(node `lem-sbc-linear-right-adjoint`). Proved 1 of 1 sorries.
No sorries remain in the item, no holes were added elsewhere, and no statement
was split off.

## No longer needed

None. No imports were removed and no nodes or modules were withdrawn.
Both existing public imports are retained for the statement, and each added
private import supplies one of the two proof terms. No planned proof dependency
is pruned: the existing source proofs perform the node's counit argument.

## Where the brief, the DAG or earlier work was wrong

None. The node already identifies both complete existing proofs and their
source locations. Its unit `sk-rem-rest` has no realized proof steps, and the
present proof changes no unit or chapter route. No change record or consumer
adaptation is necessary because only a theorem proof and private proof imports
changed.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
