## What changed

Completed `RationalBasedRetract.constant_universal_homotopy` in the item module,
following step 7 of `lem-sfb-rational-based-retract-universal-homotopy`.
Private proved helpers handle the empty positive-degree cohomology basis,
the two degree-zero retraction composites, and extension of zero and identity.
The proof checks all differential and homotopy identities by parity and verifies
all four scalar-extension formulas on finitely supported basis vectors.
Added the private proof import `Mathlib.Algebra.Group.Nat.Even`.
Removed the unused private import `Mathlib.LinearAlgebra.Basis.VectorSpace`.
All existing public signatures, definitions, attributes and public imports stay
identical. No other existing module or node changes.

The source is the existing node's constant-complex argument. The current
blueprint's direct-images paragraph (3) and the unit's route were read; this
calculation remains below that route. Searches through the prescribed msearch
LeanFinder, Loogle and grep services, and through the local adopted library and
Mathlib, found the finite-column API and homotopy constructors, but no theorem
that directly supplies this prescribed constant calculation. The proof uses
`Finsupp.lhom_ext`, `Finsupp.linearCombination_single` and `Nat.even_add_one`.

## Proved and sorry left

Closed 1 of the 2 original holes:
`RationalBasedRetract.constant_universal_homotopy`.
Added 0 holes and split off 0 statements.

The sole remaining hole is `RationalBasedRetract.universal_homotopy`, unchanged,
with node `lem-sfb-rational-based-retract-universal-homotopy` and its existing
complete seven-step proof docstring. This is a partial delivery of a module
with several holes, as permitted by the brief.

Validation: the completed constant proof passed `lcompile.py` without warnings
in 5.0 seconds. Delivery preflight recompiles the final module after removal
of the unused private import and checks declaration axioms.

The constant theorem covers arbitrary commutative rational algebras, including
the zero algebra: the proof never requests nontriviality or injectivity of the
coefficient map. Its positive-degree cohomology basis is empty; this case is
handled explicitly. Degree zero is checked separately from positive degrees.

## No longer needed

Removed private import `Mathlib.LinearAlgebra.Basis.VectorSpace`: none of the
proved constant-complex calculations uses vector-space complement existence.
No Sheaf module, DAG node or declared proof dependency is pruned. The general
theorem and its complement and homology dependencies remain open; removing
this unused proof import does not claim to bypass them.

## Where the brief, the DAG or earlier work was wrong

No mathematical errors found. The constant calculation follows the existing
step 7 without changing the statement or the unit's route. No new nodes,
statement changes, definition repairs or consumer adaptations are needed.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
