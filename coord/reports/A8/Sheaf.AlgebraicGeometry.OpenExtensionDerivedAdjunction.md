## What changed

Retired the zero-hole duplicate `Sheaf.AlgebraicGeometry.OpenExtensionDerivedAdjunction`
through `deleted.txt`, as assigned by `coord/retire-items.tsv`. Redirected the sole
node attachment, `lem-pc-open-extension-derived-adjunction`, to
`AlgebraicGeometry.exists_openExtension_derivedAdjunction` in
`WeilConjectures.AlgebraicGeometry.OpenExtensionDerivedAdjunction`. Updated the
node's Lean signature and proof wording to the upstream `Nonempty` formulation.
The node's mathematical statement and proof dependencies remain the same.

A current scan finds no consumer of the withdrawn module. The historical consumer
`Sheaf.AlgebraicGeometry.OpenExtensionProjectionFormula` is already absent, and
its upstream twin already imports the upstream adjunction module. No consumer
adaptation is needed. No upstream source file or target statement is edited.
Change record: `coord/changes/A8-retire-open-extension-derived-adjunction.md`.

Verification: the original item compiled with `lcompile.py` in 7.5 seconds.
`scratchpad/Validate.lean` compiled in 7.4 seconds, proving the exact old statement
from the upstream theorem, as well as both directions of the generic equivalence
between the two adjunction-existence formulations. The upstream theorem's axiom
print lists exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Actual original hole count: zero. Holes closed: zero; holes added: zero; split off:
zero. No `sorry` remains in the withdrawn item and no theorem with `sorry` is added.
The existing upstream `AlgebraicGeometry.exists_openExtension_derivedAdjunction`
is already fully proved, including its dependencies as checked by `#print axioms`.
This is duplicate retirement, not a newly closed proof hole.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.OpenExtensionDerivedAdjunction`.
Its duplicate declaration and local derived-category instance are withdrawn.
Its public import `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure` and
proof import `WeilConjectures.Algebra.Homology.DerivedOpenShriekAdjunction` disappear
with that copy; both remain used by the preserved upstream theorem. Neither is
claimed to be globally pruned. Node `lem-pc-open-extension-derived-adjunction`
remains and points to the upstream theorem. Its proof dependencies remain needed;
no unit statement or step is bypassed, and there are no other pruned nodes.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a module with `sorry`, but the actual queue
classifies this item as `retire` and its original module has zero holes. The
retirement row names one historical consumer which has already been retired.
The older kept-twin record warns about duplicate prerequisite environments;
those prerequisite Sheaf copies are now absent, and both the item and its twin
already import the same upstream modules. The sole remaining duplication is the
item itself. The old conclusion `∃ adj : J ⊣ R, True` and the upstream conclusion
`Nonempty (J ⊣ R)` express the same existence claim, as verified in Lean.
No false statement or unit-route error was found. No new nodes were needed.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
