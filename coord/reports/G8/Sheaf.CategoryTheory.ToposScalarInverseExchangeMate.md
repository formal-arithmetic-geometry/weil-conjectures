## What changed

Proved `CategoryTheory.ToposScalarInverseExchange.scalar_inverse_exchange_mate` in
`Sheaf.CategoryTheory.ToposScalarInverseExchangeMate` without changing its statement,
definitions, or public imports. Private helpers prove the ordinary scalar cube using
the insertion equations, then its derived cube on flat-term K-flat representatives.
Abstract categorical pasting lemmas keep the concrete comparison calculations compact.
The derived calculation respects irreducible definitions during backward inference,
preventing needless unfolding of the constant-sheaf and localization constructions.
The complete module compiled in 41.8 seconds using lcompile.py.
Counit transposition gives exchange compatibility. The supplied beta mate equalities
give the open-unit equations directly; these give compatibility of t and gamma.
The remaining helpers prove gamma normalization and naturality.

Added proof-only imports of all declarations of
`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction` and
`Sheaf.Paper.ConstantCompletionEquivalence`, plus the Mathlib slice tactic.
The latter module was already a public import; importing all exposes its proved
private resolving-class and insertion helpers only to this proof.
Updated the theorem proof docstring and the node proof and dependency list to follow
this calculation. Existing declarations keep their signatures and visibility.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.ToposScalarInverseExchange.scalar_inverse_exchange_mate`
(node `lem-pur-topos-scalar-inverse-exchange-mate`).
Holes added: zero. Holes left in the delivery: zero. No split-off statements.

## No longer needed

Removed proof imports `Sheaf.Paper.RingedTopoiTensorSections` and
`Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent`.
The item no longer needs `def-weil-pbc-ringed-tensor-section-calculus` or
`lem-trf-ringed-kflat-word-comparison-descent`: the concrete tensor hom equivalence
and direct representative calculation suffice. Removed their obsolete tool-use
entries from the node. No library module is withdrawn.

The planned dependency `lem-pur-topos-open-scalar-unit`
(`Sheaf.CategoryTheory.ToposOpenScalarUnit`) is unnecessary here: its needed unit
identity follows from the beta mate equations already assumed in `Scalars`.

## Where the brief, the DAG or earlier work was wrong

The planned general word-descent and separate open-unit arguments are valid but
unnecessary for this interface. The supplied resolving equations and beta mate
equalities give shorter direct proofs. No statement or definition repair was needed.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
