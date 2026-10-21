## What changed

Filled `WeilConjectures.exceptionalFiniteSupportExtensionMap_component_after_restriction_isIso`.
The proof obtains the normalized support mate arrow isomorphism, applies the scalar-restricted
constant-support projection consequence, and transports invertibility through the arrow-category
isomorphism. Added `Sheaf.Paper.ExceptionalSupportProjectionIso` as a strictly componentwise
intermediate theorem for the projection consequence. The item imports this proof module.

## Proved and sorry left

Proved `exceptionalFiniteSupportExtensionMap_component_after_restriction_isIso` (closed 1
sorry). The module added one named split theorem,
`WeilConjectures.exceptionalSupport_constantProjection_isIso`, whose proof remains `sorry` and
has node `lem-exc-support-constant-projection-after-restriction`. The restored dependency modules
retain their pre-existing sorries in `AlgebraicGeometry.ProEtale.isIso_constantSupportProjection`
and `WeilConjectures.supportScalarMate_projection_arrowIso`, each with its delivery node. No other
declaration was changed.

## No longer needed

No existing imports or DAG dependencies were removed. The direct component proof does not need
the unrelated right-adjoint coefficient-map declarations below it.

## Where the brief, the DAG or earlier work was wrong

The direct proof of the component theorem expands a large derived-category target and exceeds the
single-file kernel timeout. The componentwise constant-projection consequence is a strict
intermediate result, so it was split into a named theorem with its own node; the parent proof is
then a short arrow-isomorphism transport.

## New nodes

`lem-exc-support-constant-projection-after-restriction` records the strict componentwise
constant-support projection consequence and its source/search record. The corresponding module is
`lean/Sheaf/Paper/ExceptionalSupportProjectionIso.lean`.

The import-context change is recorded in `coord/changes/exceptional-adjoint-import-context.md`.

The restored dependency nodes `lem-exc-proetale-constant-support-projection` and
`lem-exc-support-scalar-projection-normalization` are also delivered with their restored source
modules and are named here because their declarations remain sorry-backed dependencies.

## Forced adaptations

The original compiler error at the current shared tip was “missing import source modules” for
`Sheaf.AlgebraicGeometry.ProEtaleConstantSupportProjection` and
`Sheaf.Paper.SupportScalarProjectionNormalization`; both imported modules had been removed from
the tip while their claims remained open. This delivery restores their exact source files without
changing declarations, because the assigned item cannot compile without them. No lines in their
proofs or interfaces were altered.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
