## What changed

The item now combines the ordinary finite-ring diagonal-factor square with the integrated
closed-section specialization square. Its declaration and docstring are unchanged. The diagonal
square is proved using the existing private mate-pasting and section-compositor calculations in
Sheaf.Paper.DiagonalExchangeCube, accessed by a proof-only `import all`.

The new module Sheaf.Paper.FiniteSectionIntegratedSpecialization constructs the actual integrated
zero specialization using inverse normal-section comparison and inverse integration adjunct.
It proves normalSectionMap_isIso and integratedSpecialization_normalization. The parent proof
unpacks both supplied normalization equations, cancels the invertible integration factors,
composes the two squares and proves the inverse-orientation formula by cancellation.

## Proved and sorry left

Closed the original body of
AlgebraicGeometry.ProEtale.SmoothPurityBaseChange.finite_orientation_base_change
(node lem-sp-finite-normalized-orientation-base-change), by decomposition.

Added one remaining hole:
AlgebraicGeometry.Etale.FiniteSmoothPurity.integratedSpecialization_baseChange
(node lem-sp-finite-section-integrated-specialization-base-change).
It is strictly the section DNC/integration factor, with no diagonal exchange or smooth-morphism
orientation. The two invertibility/normalization helpers and the parent diagonal-factor square
are complete Lean proofs. Holes closed: 1; holes added: 1; net: 0. No other sorry is left
in the delivery. No data are chosen from an uncharacterized existence statement.

## No longer needed

No existing public import is removed. The two added imports are proof-only.

The item no longer needs lem-sp-section-dnc-integration-square
(Sheaf.Paper.SectionDncIntegrationSquare): its coefficient-setting pro-etale formulation is
replaced here by the ordinary arbitrary-finite-ring section square in the new module.

The item no longer needs det-sp-finite-general-ring (Sheaf.SecSmoothPurity.FiniteGeneralRing),
lem-pur-dnc-coefficient-transport (Sheaf.SecSmoothPurity.PurityDncCoefficientTransport), or
lem-sp-orientation-scalar-tower-transport (Sheaf.Paper.OrientationScalarTowerTransport).
The diagonal mate calculations and the new section square work directly at A, so no reduction
to a prime-power coefficient presentation and no scalar-extension transport are used.

The item no longer needs thm-weil-pbc-site-comparison
(Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit): all equalities are proved in ordinary
etale coordinates. These are dependency removals from this item's proof, not withdrawals of
existing modules or declarations; other users of those modules are unaffected.

## Where the brief, the DAG or earlier work was wrong

The original plan passes through prime-power coefficient transport and site reflection.
The existing diagonal cube's private proved calculations already apply to arbitrary finite A
in ordinary etale coordinates. They can be reused without those changes of presentation.
The existing integrated-section square is stated in PurityFiniteSetting/pro-etale coordinates,
so it does not directly typecheck against the supplied ordinary finite-ring normalization.
The new remaining statement isolates precisely that section factor, independently of a diagonal.

The edge cases of the new statement retain positive annihilator N and allow d=0, empty schemes,
zero A, identity base change, and non-flat b. The maps are canonical even when the supplied
geometry and Cartesian witnesses differ, because those witnesses are propositions.

## New nodes

lem-sp-finite-section-integrated-specialization-base-change records the integrated section square
and its three proved construction/normalization declarations. Its source is proof (1) of the
latest blueprint's smooth-purity base-change factors. The complete remaining proof is recorded
in its theorem docstring and its four DAG proof steps. No existing interface is changed and no
change record is required.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
