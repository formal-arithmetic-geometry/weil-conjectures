## What changed

Proved `AlgebraicGeometry.Scheme.adicComparison_composition` with its original
statement. The proof follows the existing flat-term K-flat representative route:
transport the normalized scalar-composition equations to the specified composite,
paste those equations with the three scalar/geometric comparison equations,
and cancel the computation isomorphisms. Resolving-class naturality extends the
result to all derived objects. A final categorical cancellation gives the
required equation of inverse comparisons.

Added `Sheaf.Paper.AdicOrdinaryComparisonComposition`, containing the constructed
`adicOrdinaryChangeComp` and the proved ordinary composition theorem
`adicOrdinaryComparison_composition`. Its proof constructs the composite ordinary
comparison, verifies its insertion normalization, and invokes the existing
uniqueness theorem. The generic insertion and derived pasting calculations are
proved private helpers. No shared definition or statement was changed.

The item now privately imports this ordinary module and uses private proof APIs
from `AdicFiniteReductionData` and `ConstantCompletionEquivalence`. Its public
imports and declaration signature stay unchanged. The original DAG node and the
new ordinary node record these arguments.

Validation: `lcompile.py --all` compiled both delivered modules without warnings;
the ordinary module took 18.6 seconds and the item took 45.0 seconds, each below
the 60-second file limit. A direct text comparison confirms the original theorem
signature is unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.adicComparison_composition`.

Also proved `AlgebraicGeometry.Scheme.adicOrdinaryComparison_composition`;
`AlgebraicGeometry.Scheme.adicOrdinaryChangeComp` is an explicit equality transport
of the already constructed ordinary balancing isomorphism.

Original holes closed: 1. Holes added: 0. Holes remaining in the delivered Lean
modules: 0. No theorem is split off with `sorry`, and no definition contains a hole.
The proof uses the existing normalization and K-flat computation APIs, with no
additional mathematical hypotheses. Zero rings, identity maps and zero complexes
are included; the proof uses no nontriviality assumption.

## No longer needed

None. No existing import, node or module is withdrawn. The original K-flat
resolution, change-of-rings and geometric-pullback dependencies remain needed
through the computation APIs of `AdicFiniteReductionData`. The unit's route is
preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction to the statement or the unit route was needed.
The ordinary comparison coherence implicit in the DAG's second proof step is
now made explicit and proved. Equality transport and composition normalization
needed careful local transparency settings to avoid expanding large sheaf and
derived-category definitions during kernel checking. These settings are local
to the delivered files and do not change a shared interface.

## New nodes

`lem-sfb-adic-ordinary-comparison-composition` records the ordinary comparison
coherence used termwise in the derived proof. Both its balancing transport and
its theorem are fully proved in the new module; it leaves no new proof item.
The Mathlib searches found ordinary scalar reassociation and adjunction uniqueness
but no equation for these chosen normalized geometric/scalar comparisons.
LeanSearch was unavailable, as recorded by the search tool. No change record is
needed because no existing definition or statement is changed.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
