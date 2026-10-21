## What changed

Proved `CategoryTheory.Mod.internal_tensor_composition_unit_normalization` using the
specified composite and direct extension/restriction adjunctions. Chose their
`leftAdjointUniq` comparison, extracted its unit equation on underlying arrows,
and used module linearity and the existing action/unit identities to establish
the multiplication and inverse formulas. The comparison with
`extendScalarsComp.symm` follows from the source definitions.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.Mod.internal_tensor_composition_unit_normalization`
(node `lem-sfb-internal-tensor-composition-unit-normalization`).
No holes added; no `sorry` remains in the delivered module. No split-off statements.
The complete module compiles cleanly through `lcompile.py` (4.7 seconds), after
removing the redundant private imports.

## No longer needed

Removed the redundant private imports
`WeilConjectures.CategoryTheory.RingObjects.RingPresheaf`,
`Mathlib.CategoryTheory.Monoidal.Mod`, and
`Mathlib.CategoryTheory.Limits.HasLimits`. All the required declarations already
come from the retained public imports. No mathematical dependency nodes or modules
are withdrawn. The proof follows
the existing plan using already proved source-library identities.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair was needed. The tensor identities are internal
ambient morphism equations, so the proof uses neither elements nor a concrete
category assumption. The specified adjunctions and all original hypotheses remain.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
