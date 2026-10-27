## What changed

The final `twist_frobenius_scalar` theorem is now proved by conjunction introduction from four named component theorems. The component theorems isolate the finite/integral, rational/common-stage, reduction/localization, and field-extension clauses. The existing signed quotient and reduction sheaf comparison declarations are unchanged.

## Proved and sorry left

Closed one sorry: `WeilConjectures.TwistFrobeniusScalar.twist_frobenius_scalar`.

The following six named theorem holes remain, each with a DAG node and source documentation: `signedQuotients_existsUnique`, `reductionSheafLine_existsUnique`, `twist_frobenius_scalar_finite_integral`, `twist_frobenius_scalar_rational_qbar`, `twist_frobenius_scalar_reduction_localization`, and `twist_frobenius_scalar_field_extensions`. Four of these are split-off component statements strictly below the parent conjunction; the first two were existing holes.

## No longer needed

No imports or existing proof-dependency nodes became unnecessary. The original module imports remain required by the definitions and component statements.

## Where the brief, the DAG or earlier work was wrong

The original node's proof plan treated the full conjunction as one unresolved assembly theorem. The assembly is a direct conjunction of four independently stated component results, so those components are recorded as new split nodes while the target theorem itself is closed. No target statement or definition was changed.

## New nodes

`lem-pur-twist-frobenius-scalar-finite-integral` records the finite and integral clauses.

`lem-pur-twist-frobenius-scalar-rational-qbar` records the rational and common-stage clauses.

`lem-pur-twist-frobenius-scalar-reduction-localization` records finite reduction and integral localization compatibility.

`lem-pur-twist-frobenius-scalar-field-extensions` records finite-field and algebraic-closure scalar extension compatibility.

The interface change record is `coord/changes/reductionH.md`.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
