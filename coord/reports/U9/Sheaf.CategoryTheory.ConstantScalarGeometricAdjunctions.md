## What changed

Proved `CategoryTheory.constant_scalar_geometric_adjunctions` with its existing statement.
Private helpers calculate constant scalar sections, prove linearity of the underlying
comparison, and establish the adjunction square and its Hom, unit, and counit equations.
The same adjunction-square proof supplies the further-left-adjoint comparison.
The module compiles in 20 seconds; the private scalar comparison uses a local heartbeat
allowance for the bundled restriction-of-scalars reduction. Updated the node proof to match this argument. No public definitions or signatures change.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.constant_scalar_geometric_adjunctions`
(`lem-sfb-constant-scalar-geometric-adjunctions`). Added zero holes; zero remain in this module.
No statements were split off. The proof uses the existing constant-ring restriction equivalence.

## No longer needed

Removed the unused proof imports `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`,
`Mathlib.CategoryTheory.Sites.CoverLifting`, and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`.
The corresponding proof dependencies `lem-weil-pbc-ringed-topoi-module-adjunction`,
`def-pur-localized-ringed-site`, and `lem-weil-pbc-site-constant-restriction` are unnecessary
for this theorem: its ringed and further-left adjunctions are supplied as arguments, and
its statement is already uniform over arbitrary small sites. The ringed-adjunction node
remains a statement dependency describing the supplied adjunction, but its existence theorem
is not used to prove this conditional comparison. Removed only that node's obsolete
`tool_uses` approval; retained the constant-ring equivalence approval.
No modules are withdrawn and no unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned intermediate transported adjunction is unnecessary: Mathlib's mate equivalence,
full faithfulness, essential surjectivity, and coyoneda prove the adjunction square directly.
The original hole's statement requires no separate localization equation or construction.
No mathematical statement or definition was repaired.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
