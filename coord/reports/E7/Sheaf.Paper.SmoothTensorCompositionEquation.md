## What changed

Proved `AlgebraicGeometry.ProEtale.smoothTensorCompositionEquation` without changing its
statement or the three constructed comparison definitions. Added private proof imports of
`Sheaf.AlgebraicGeometry.CompactificationProjectionComposition`,
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence`, and
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormulaCoherence`.

The tower projection identity transports along the three compactification comparisons by
naturality and cancellation. This gives projection compatibility for the specified
`smoothCompactSupportCompIso`. The existing tensor-composition theorem then applies to its
adjunction-induced exceptional comparison. Private categorical lemmas perform the unit
specialization, using tensor associativity, naturality in the coefficient variable, and
the left-unitor identity. No arbitrary composition comparison is chosen. The transport and
unit calculations are checked first for abstract functors; the geometric specialization
then applies them to the existing canonical maps. Typed projection components and an
explicit structural congruence proof prevent repeated expansion of the derived
constructions; the congruence method follows the source library
`EtaleOpenInjectiveLerayEdge`. Every generated proof is checked by the Lean kernel.

The complete module compiled through `lcompile.py` in 29.9 seconds, with no warnings.
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`. The
original three comparison definitions and the theorem signature were checked verbatim.
The profiling commands, axiom-printing command, and scratch files were removed before
delivery.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.ProEtale.smoothTensorCompositionEquation`
(node `lem-v8-smooth-tensor-composition-equation`). Added zero holes; zero holes remain in
this module. All private helper lemmas are proved.

## No longer needed

None. Both declared proof dependencies are used:
`lem-route-projection-map-associativity` and
`lem-amb-compactification-projection-composition`. No existing imports, nodes, or modules
are removed. The proof follows the existing node plan and preserves the unit route.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The assertion needs no smoothness hypothesis: the
finite-coefficient projection formula and the specified comparison constructions suffice,
as its existing Lean signature and docstring already state. No new nodes or statement
repairs are required.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
