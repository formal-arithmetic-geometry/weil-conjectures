## What changed

Proved `smooth_localAcyclicity` by reducing its universal and ordinary clauses to the
strict-local core theorem `smooth_localAcyclicity_core`. Added the core module and its DAG node;
updated the item's proof and dependencies to record this route.

## Proved and sorry left

The target theorem `AlgebraicGeometry.Etale.smooth_localAcyclicity` is proved. The strict-local
calculation is split off as `AlgebraicGeometry.Etale.smooth_localAcyclicity_core`, whose proof
remains `sorry` and is recorded by node `lem-weil-pbc-smooth-local-acyclicity-core`.

## No longer needed

The item proof no longer directly needs the strict-local exchange, fibre, coefficient, stalk,
and adjunction declarations listed in the original proof plan; they remain dependencies of the
split core node. No existing imports were removed from the item module.

## Where the brief, the DAG or earlier work was wrong

The original item bundled the universal assembly with the full strict-local cohomology argument.
The assembly is a short formal consequence of smoothness stability under pullback, so the strict
local calculation was separated into a strictly smaller theorem.

## New nodes

`lem-weil-pbc-smooth-local-acyclicity-core` records the strict-local calculation needed to prove
local acyclicity for a smooth morphism. Its source is Stacks Tag 0GJQ, and its complete proof
plan is inherited from the original item's strict-local steps.

The import adaptation is recorded in `coord/changes/smooth-local-acyclicity-core-import.md`.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
