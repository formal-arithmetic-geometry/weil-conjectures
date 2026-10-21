## What changed

Proved `AlgebraicGeometry.Scheme.constant_periodic_resolution_nonzero` without
changing its statement or any existing definitions. Private proved helpers establish
exactness of the sized constant-module functor and its rank-one identification with
the unit module directly from Mathlib. Algebraic exactness is mapped through this
functor; the existing scalar periodic-resolution theorem supplies the complex,
termwise flatness and K-flat augmentation. A generic private transport theorem carries out the term identifications and
augmentation equations without unfolding the large site construction. A cokernel
isomorphism transports the augmentation to the prescribed constant quotient. Local injectivity of additive
sheafification and the pro-etale covering condition prove injectivity of constants
and nonvanishing on nonempty schemes.

Validation: the complete module compiled through `lcompile.py` in 23.1 seconds.
The assigned theorem signature is byte-identical to the original.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.constant_periodic_resolution_nonzero`.
No holes added. No `sorry` remains in the delivered module. The existing imported
`SheafOfModules.exact_scalar_periodic_resolution` remains an independent proof item.

## No longer needed

Removed private proof imports `Sheaf.CategoryTheory.FiniteTypeConstantExact` and
`Sheaf.CategoryTheory.SiteConstantModuleUnit`. Their nodes
`lem-weil-pbc-finite-type-constant-exact` and
`lem-sf-constant-module-unit-locally-bijective` are unnecessary for this proof:
the required sized instances and local injectivity follow directly from Mathlib.
This is pruning of this item's proof dependencies only; neither module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned general exactness and unit lemmas use a common small-site/coefficient
universe, whereas this item's statement keeps coefficient and scheme universes
independent. The proof establishes the needed sized versions privately rather than
altering either public interface. The mathematical argument and all edge cases are
unchanged: the zero ring and empty base are allowed, and only the nonvanishing
clauses require a nonempty base and a nontrivial quotient.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
