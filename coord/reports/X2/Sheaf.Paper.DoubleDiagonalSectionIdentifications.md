## What changed

Proved `WeilConjectures.PurityFiniteSetting.DiagonalPasting.doubleDiagonalGeometry`
and `doubleDiagonalProperties` in `Sheaf.Paper.DoubleDiagonalSectionIdentifications`.
The geometry proof constructs the lifts for the three nontrivial Cartesian squares and
checks both projections; the fourth square is the defining pullback. All seven section
identities follow by projection calculations. The properties proof transports smooth
relative dimension, separatedness, local finite type and quasi-compactness across the
first square, then uses projection and composition instances.

Added a private proof import of
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` for its relative-dimension
projection instances. Existing signatures, public imports and definitions are unchanged.
The two completed declarations are verified by the item compilation and the delivery
axiom probe.

## Proved and sorry left

Closed two of the three original holes:

- `WeilConjectures.PurityFiniteSetting.DiagonalPasting.doubleDiagonalGeometry`.
- `WeilConjectures.PurityFiniteSetting.DiagonalPasting.doubleDiagonalProperties`.

One original hole remains, as a complete public theorem body `:= by sorry`:
`WeilConjectures.PurityFiniteSetting.DiagonalPasting.doubleDiagonalSectionIdentifications`
(node `lem-pur-double-diagonal-section-identifications`). Its existing docstring and DAG
steps give the full counit-mate and section-compositor argument. No new holes or nodes
were added. This is a partial proof delivery, not a decomposition. The third restriction
identity is the defining formula for `alpha`; the first two still require the horizontal
base-change pasting calculation and derived pullback coherence.

## No longer needed

Removed private imports `Sheaf.Paper.SmoothExceptionalTensorPasting` and
`Mathlib.AlgebraicGeometry.ZariskisMainTheorem`: neither is used by the two completed
proofs or the existing signatures. The remaining theorem's mathematical proof still
needs the smooth exceptional pasting dependency in its DAG; this delivery does not
withdraw that node or claim the entire pasting route is pruned. No public import,
DAG node, or library module is withdrawn. No closed-immersion/properness theorem is
needed to prove the geometry and permanence declarations themselves.

## Where the brief, the DAG or earlier work was wrong

The relative-dimension base-change result in Mathlib is a lemma giving an instance,
not a globally registered instance in this context. The proof installs
`smoothOfRelativeDimension_isStableUnderBaseChange` explicitly; the source-library
Smooth extension provides the projection instances. This is an implementation detail,
not a change to the mathematical statement or unit route.

A scratch import of the published item encountered a duplicate declaration in the
published dependency closure (`SmoothDuality.Local` versus
`EtaleDerivedJointlySurjectiveConservative`). The actual item source compiled initially,
and later item-source compilation checked the new proofs. No source-library change
or workaround is part of this delivery.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
