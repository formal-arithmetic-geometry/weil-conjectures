## What changed

Proved `WeilConjectures.IntegralAmbient.pullTowerModel`. At each finite quotient, the
projection square identifies the two right adjoints, so uniqueness of left adjoints produces
the comparison. Its unit equation gives normalization. Finite linearity extends normalization
to every scalar. Composite-unit extensionality along the locally surjective coefficient
projection proves compatibility with each recorded quotient transition and uniqueness of the
whole natural strict tower isomorphism. No K-flatness or other extra hypothesis is used.

After profiling the combined file at 81.4 s and abstracting its costly restricted-map
extensionality argument, moved its self-contained pullback presentation and proved comparison
into `Sheaf.Paper.NormalizedIntegralPullbackTower`. The item publicly reexports every original
name with exactly the same signature, visibility, instance attributes and definition body.
Tensor and derived-comparison proofs are unchanged. The new module imports the existing
normalized scalar adjunction and unrestricted reduction transition API. The two nodes describe
the actual proof route. Change record: `coord/changes/B4-normalized-integral-pullback-tower.md`.

## Proved and sorry left

Closed the one original hole: `WeilConjectures.IntegralAmbient.pullTowerModel`, now attached to
`lem-pur-normalized-integral-pullback-tower`. Holes closed: 1 of 1. Holes added: 0.
No `sorry` remains in either delivered Lean module. All supporting helpers are proved.
The original `integralAmbientOperationModels` proof is preserved.

Validation: the new support module compiled in 47.8 s; the remaining item module compiled
in 48.2 s. All nine original direct importers compiled against the reexported interface,
with no adaptations. The unchanged validation copies were removed.
`#print axioms WeilConjectures.IntegralAmbient.pullTowerModel` lists exactly `propext`,
`Classical.choice`, `Quot.sound`. The ambient derived theorem still has a pre-existing
transitive `sorryAx` dependency; this delivery introduces none.

## No longer needed

Removed `lem-pur-strict-coefficient-comparison-calculus` from this node's proof dependencies
and obsolete top-level `tool_uses` entry. Neither its module nor its generalized coefficient
calculus is used or imported by this proof. Its declaration remains in the library; this
packet makes no claim that other consumers no longer need it. No original public import is
removed. The item no longer directly imports PullbackExistsOfUniverses or
CompletedCoefficientRingedCoherence: their uses moved to the support module. The new support module omits the tensor, derived descent and Roos proof imports,
which it does not use. No Lean module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned strict coefficient calculus is unnecessary for the pullback clause: the existing
normalized scalar adjunction and recorded transition formulas suffice. The original statement
is unchanged and true, including empty sites, the initial quotient index, arbitrary scheme
morphisms, independent universes and unbounded complexes. No inverse image of a completed
coefficient limit is identified with the completed coefficient sheaf on the source. The new
node is a proved strict-tower part of the existing argument; the unit route stays intact.

The repository's older brief prohibits splitting slow files, while the explicit worker
instructions dated 2026-10-26 permit splitting after improving slow definitions. This packet
follows the explicit instructions, first abstracting the expensive extensionality proof and
then isolating the self-contained proved pullback presentation.

## New nodes

`lem-pur-normalized-integral-pullback-tower` is the existing strict pullback tower clause,
including its canonical coefficient map and ordinary pullback presentation, now fully proved
in its own module. It is strictly part of the ambient derived operation comparison. It adds
no hole and has no dependency on its parent item. The original node now imports this proved
step; the tensor and localization steps are preserved.

Change record: `coord/changes/B4-normalized-integral-pullback-tower.md`.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
