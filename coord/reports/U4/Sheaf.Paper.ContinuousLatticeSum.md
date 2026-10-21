## What changed

Proved `AlgebraicGeometry.ProEtale.continuous_lattice_sum` from the algebraic
basis clause of the existing `Padic.finite_sum_lattice` theorem. Lifted the
basis vectors to the product of the input lattices and extended these lifts
linearly to construct the continuous section. Postcomposition gives the
continuous-function lifting and the sectionwise range equality. Mathlib's fpqc
continuous-function sheaf theorem supplies the sheaf conditions. Pointwise basis
coordinates give the restriction-compatible trivialization; Mathlib's finite
power tensor equivalence gives the scalar-extension comparison, with its actual
pure-tensor formula proved explicitly.

The public theorem signature and the lattice inclusion definition are unchanged.
Updated the node proof and proof dependencies to follow the implementation.
Local irreducibility annotations and proved evaluation equations keep the private
coordinate constructions and the coefficient ring folded during elaboration.
The import change record is `coord/changes/continuous-lattice-sum-imports.md`.
No other library module is changed. The authorized remote compiler checked the
complete module successfully in 38.0 seconds, with no errors or warnings.
A textual comparison confirmed the original public theorem signature and
inclusion definition are unchanged; all lines are at most 100 characters.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.continuous_lattice_sum`
(node `lem-sfb-continuous-lattice-sum`). Holes added: zero. Split off: zero.
No `sorry` remains in the module; every private helper is proved.
The existing imported `Padic.finite_sum_lattice` remains a proof dependency;
this delivery does not claim to close its hole.

## No longer needed

Only the simultaneous algebraic basis clause of `Padic.finite_sum_lattice` is
needed. Its explicit spectral-topology homeomorphism clause is unused:
continuity follows directly from field coordinates in the ambient norm topology.
The unit's finite-lattice-sum route is preserved. No module is withdrawn.

Removed the public imports `Sheaf.Paper.ContinuousIntegralCoefficients`,
`Sheaf.CategoryTheory.RingedSiteModules`, and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`. Replaced the
direct public import `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` by
`Sheaf.NumberTheory.Padics.CoefficientExtension`; the former remains a transitive
dependency of `FiniteSumLattice`. Added direct public Mathlib imports for tensor
definitions and continuous-map algebra, and private proof imports.

The node proof no longer uses
`def-weil-pbc-continuous-integral-coefficients`,
`def-weil-sheaf-of-modules-category`, or `def-pur-sheaf-tensor-product`.
Their statement dependencies are preserved. The recorded coefficient subring,
Mathlib continuous-function sheaf theorem, range equality, and ordinary tensor
equivalence prove the existing sectionwise statement directly.
`tools/downstream.py Sheaf.Paper.ContinuousLatticeSum` reports zero current
Lean importers; the planned DAG parents still need this item.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's missing compiled Mathlib artifact error no longer occurs.
Remote compilation initially encountered a busy server, then became available.
The retained draft used the nonexistent `Continuous.apply`; coordinate continuity
now uses `continuous_apply` composed with the appropriate continuous map.

The theorem's scheme and arbitrary test-space universes are independent. The
range proof constructs its lifted functions on each scheme object directly,
instead of reusing a local statement fixed at the arbitrary test-space universe.
Finite empty coordinate sets (rank zero), empty test spaces, and singleton input
families are covered by the finite basis, sum, and tensor constructions without
extra assumptions.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
