## What changed

The item module now proves `Algebra.isNormal_tensorProduct_of_geometricallyNormal` by reducing prime localizations to the normal-domain case. Localization, tensor base-change, normality transport across ring equivalences, and filtered tensor colimit infrastructure are implemented in the module. The remaining domain argument is isolated as `Algebra.normal_domain_case`.

## Proved and sorry left

Proved: `Algebra.isNormal_tensorProduct_of_geometricallyNormal`.

Sorry left: `Algebra.normal_domain_case`, split off as node `lem-weil-pbc-geometrically-normal-tensor-normal-domain-case`.

## No longer needed

The original eleven-step DAG route is pruned below the new domain-case split; the direct scheme normalization declarations are not used by the compiled reduction.

## Where the brief, the DAG or earlier work was wrong

The DAG described a fully expanded finite-type/intersection proof, but the available library provides the localization and filtered-colimit infrastructure directly. The target can be reduced to a strictly stronger normal-domain theorem with fewer dependent steps.

## New nodes

`lem-weil-pbc-geometrically-normal-tensor-normal-domain-case` records the remaining normal-domain theorem and its source proof route.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
