## What changed

Proved `AlgebraicGeometry.finiteCoefficient_boundedBelow_ctf_reflection` in
`Sheaf.Paper.BoundedBelowCtfReflection`. The proof constructs the invertibility of `l` on
all residue fields from the finite-field datum, reflects the Tor interval using
`finiteCoefficient_comparison_reflects_torAmplitude`, and invokes the new constructibility
reflection module. Added the proved helper theorem
`AlgebraicGeometry.finiteCoefficient_boundedBelow_constructible_reflection`, using the
finite-ring essential-image criterion, derived realization composition isomorphisms, and
bounded-below comparison full faithfulness.
The proof-only imports and linter setting are recorded in
`coord/changes/E3-bounded-below-ctf-reflection-proof-import.md`.

## Proved and sorry left

Closed the original theorem
`AlgebraicGeometry.finiteCoefficient_boundedBelow_ctf_reflection` (one sorry closed).
The helper theorem
`AlgebraicGeometry.finiteCoefficient_boundedBelow_constructible_reflection` is also fully
proved; no sorry remains in either delivered module.

## No longer needed

No proof-dependency imports were removed. The original direct exact/full-faithfulness plan
is subsumed by the existing finite-ring essential-image theorem and the comparison Tor
reflection theorem; no additional modules or nodes are needed beyond those imported by the
helper proof.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan omitted the already proved finite-ring essential-image criterion as a
usable route and treated the constructibility reflection as an informal sheaf-by-sheaf
argument. The delivered proof uses the stronger existing essential-image characterization,
while preserving the same bounded-below comparison route and conclusion.

## New nodes

Added `lem-sf-bounded-below-constructible-reflection`, carrying the helper theorem and its
proof dependencies.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
