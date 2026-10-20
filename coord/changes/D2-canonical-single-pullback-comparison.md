# Make the adopted-source compatibility repair explicit

## Reason

The rework row for this item records an environment collision in the
quarantined implementation: importing the old Sheaf derived-pullback module
and the adopted source module redeclared `AlgebraicGeometry.derivedPullback`.
The live repair is a compatibility import of the adopted source. This delivery
makes that repaired module explicitly use `autoImplicit false` and documents
why it must not redeclare the source construction.

## Old

The compatibility module imported the adopted source and relied on the
project-wide option defaults. Its public interface was already the source
interface, but the repair rationale was implicit in the file.

## New

The module keeps the same public import and adds a module-scoped
`set_option autoImplicit false` plus documentation stating that the source
module owns the declarations and the `derivedPullback` construction. The
module compiles and all declaration signatures remain unchanged.

## Users

No downstream module is changed. Existing importers continue to receive the
same three declarations from the public compatibility import. The change is
module-scoped and introduces no new names or assumptions.

## Status

landed 20261020T221111-L-4143921 2026-10-20 (merge of deliver/D2/Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison)
