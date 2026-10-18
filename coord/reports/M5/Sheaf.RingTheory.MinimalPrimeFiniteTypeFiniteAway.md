## What changed

Copied the target module into the M5 sandbox, added the proof-only import
`Sheaf.RingTheory.MinimalPrimeFiniteTypeFiniteAwayAux`, and proved the target by converting its
explicit finite spanning-family intermediate statement into `Module.Finite`.

Added the new auxiliary module and its DAG node. The auxiliary statement isolates the strict
monomial-spanning part of the Stacks Tag 02ML argument and remains a named sorry for follow-up.

## Proved and sorry left

Closed `RingHom.exists_finite_awayMap_of_finite_fiber_minimalPrime` (1 hole).

Left `RingHom.exists_finite_span_awayMap_of_finite_fiber_minimalPrime` as one split-off sorry;
its node is `lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away-aux`.

## No longer needed

The target module no longer imports these proof-only modules directly:

- `Mathlib.RingTheory.Localization.AtPrime.Basic`
- `Mathlib.RingTheory.KrullDimension.Zero`
- `Mathlib.RingTheory.Ideal.Maps`
- `Mathlib.RingTheory.Nilpotent.Lemmas`
- `Sheaf.RingTheory.FiniteTypeAlgebraFiniteSpectrum`

The auxiliary node retains the finite-spectrum, fibre-localization, minimal-prime and
locally-nilpotent declarations in its planned proof dependencies, so those nodes remain needed
for proving the split-off theorem.

## Where the brief, the DAG or earlier work was wrong

The target node's proof dependencies have no Lean attachments in the current checkout, so the
full polynomial argument cannot be elaborated from declarations currently available. I isolated
that missing strict subargument as the auxiliary node above; the target proof itself is complete.

The target DAG copy now records the auxiliary node as its sole proof dependency, matching the
Lean proof route.

## New nodes

`lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away-aux` in
`dag/nodes/sec-proper-base-change/`.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
