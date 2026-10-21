## What changed

Replaced the four proof holes in
`Sheaf.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients` with direct proofs.
The ideal restriction proof uses the singleton-span criterion, preservation of
powers and naturality of the global section. The quotient identity and
composition proofs lift a quotient class and use the corresponding functor law
of B. Projection naturality is the defining formula of the quotient map.

All existing statements, definitions, attributes and imports are preserved.
No consumer adaptations or changes of the proof route are needed.

## Proved and sorry left

Closed all four original holes:

- `CategoryTheory.sectionPowerIdeal_restrict`
- `CategoryTheory.sectionPowerQuotientMap_id`
- `CategoryTheory.sectionPowerQuotientMap_comp`
- `CategoryTheory.sectionPowerQuotientProjection_naturality`

There are zero textual sorries left and zero added or split off.
The complete module compiles cleanly through `lcompile.py` in 1.1 seconds.
An independent scratch copy with `#print axioms` for all ten declarations
compiles in 1.3 seconds and reports only `propext`, `Classical.choice`, and
`Quot.sound`. The proofs use existing Mathlib and the original definitions.

## No longer needed

None. All three existing imports are used by the definitions or statements.
There are no DAG proof dependencies to prune, and no new imports or nodes.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The formulas include exponent zero and do
not require a nonzero section, injectivity of multiplication, or enough points.
A temporary compile-service failure involving missing Mathlib artifacts
resolved during the session; the final module compiles successfully.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
