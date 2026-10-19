## What changed

Proved `AlgebraicGeometry.ProEtale.IntegralConstantCompletion.integral_constant_completion`
without changing its signature or any public definition. Added proved private helpers for
Noetherianity, principal image ideals, finite kernels, the reflector inverse, and transport
of the scalar adjunction between homotopy and cochain localizations. The existing general
completion comparisons and normalized coefficient adjunction supply the mathematical inputs.
Updated the item's proof plan and direct proof dependencies to the actual argument.

Validation: remote `lcompile.py` recompiled the retained final module against the current
published build on 2026-10-19, cleanly in 8.8 seconds,
with exit code 0 and no warnings. The delivery dry run supplies the remaining
mechanical checks.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.ProEtale.IntegralConstantCompletion.integral_constant_completion`
(node `det-prop-integral-criterion-constant-coefficients`).
There are zero holes left in the item, zero added holes, and no split-off statements.
The existing imported dependency theorems remain the planned stage-3 inputs; their proofs
were not changed in this delivery.

## No longer needed

Removed proof-only imports:
- `Mathlib.RingTheory.Noetherian.Defs` (already public through the general completion module).
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` (no direct use).
- `Sheaf.Paper.CompletedConstantSheafReduction`.
- `Sheaf.Paper.ConstantModuleSectionProperties`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`.
- `Sheaf.Paper.WeilCompletedTensorReflector`.

The direct proof no longer separately uses nodes
`lem-weil-pbc-completed-constant-sheaf-reduction`,
`lem-weil-pbc-constant-module-section-properties`,
`lem-weil-pbc-ringed-topoi-module-adjunction`,
`lem-weil-pbc-exact-functor-derived-factorization`,
`lem-weil-pbc-exact-functor-derived-functor`,
`lem-pc-derived-adjoint-functors`, and
`lem-weil-pbc-ringed-koszul-completion-reflector`.
The general completion module already packages the flatness, finite kernels and reflector;
the normalized coefficient adjunction packages the scalar adjunction. Some removed modules
remain transitive inputs of those existing packages, so this is direct dependency pruning,
not a claim that their entire modules leave the targets' closure.
`def-weil-pbc-noetherian-ring`, `def-weil-pbc-proetale-site`,
`det-prop-sfb-qlbar-colimit-x-integral-limit`, `sk-def-pe-derived-completion`, and
`def-pc-sheaf-restrict-scalars` remain statement dependencies; their separate proof edges
are unnecessary because the statement already fixes the actual site, rings and unit.
All public imports are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was necessary. The declared adjunction dependencies
are available through the more directly usable existing normalized coefficient adjunction
(node `lem-pur-sheaf-ring-derived-coefficient-adjunction`). Its homotopy-level universal pair
must be transported to the cochain-level pair used by `extend`; the private helpers perform
that transport, rather than assuming the selected derived functors coincide.
The blueprint unit route is retained: constant/completed coefficients, finite reductions,
complete-category restriction, and the specified inverse all remain in the proof.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
