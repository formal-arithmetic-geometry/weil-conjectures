## What changed

Filled `WeilConjectures.SemilinearSections.ordinaryInverseSystem_exists` in
`Sheaf.Paper.SemilinearOrdinaryInverseSystem`, preserving its statement and the public
`OrdinaryInverseSystem` structure. The new source extraction construction is in
`Sheaf.Paper.SemilinearOrdinarySourceStrictSystem`; the other supporting constructions and
lemmas are private to the item.

The adjacent ring squares define a natural transformation of ring towers, yielding the
square for every pair of indices. The existing proved scalar-restriction comparison gives
normalized comparisons. Transporting strict transitions through those comparisons produces
an actual functor on strict systems; its underlying-sheaf formula proves the identity and
composition laws. The source strict system uses the existing evaluations and transitions
exactly. The proved strict-system/sequence-site equivalence reassembles the output, and its
sectionwise identity isomorphisms give the required component normalization and transition
equation. A conservative family of exact evaluations detects finite limits and colimits,
so the assumed level exactness proves exactness of the assembled functor.

Added proof imports of `Sheaf.CategoryTheory.InverseImageScalarRestrictionComparison`,
`Sheaf.CategoryTheory.SystemRingedSequenceSite`, and
`Mathlib.CategoryTheory.Functor.ReflectsIso.Limits`, and
`Sheaf.Paper.SemilinearOrdinarySourceStrictSystem`.

Profiling found repeated elaboration of the coefficient transports in the prescribed
source-transition laws. A section-map wrapper avoids the original heartbeat failures.
After this optimization the complete file checked in 70–74 seconds, so the already proved
source extraction was moved into its own construction module, as permitted by step 3a.
No shared definition or existing module other than the item was changed.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.SemilinearSections.ordinaryInverseSystem_exists`
(node `lem-coef-ordinary-inverse-system`). No holes added or split off. No `sorry` remains
in either delivered Lean module.

Validation: `lcompile.py --all` compiled the source construction in 31.6 seconds and
the item in 50.8 seconds. Both `#print axioms` checks show only `propext`,
`Classical.choice`, and `Quot.sound`.

## No longer needed

None. All declared dependencies of `lem-coef-ordinary-inverse-system` are used. No existing
public import, module, declaration, or DAG dependency is removed.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair was needed. The existing proved scalar-restriction
comparison and sequence-site equivalence suffice for the planned construction; no further
existence theorem or split-off obligation is necessary. The arbitrary inverse-image
functor need not have a right adjoint for this inverse-image-only result.

## New nodes

`def-coef-ordinary-source-strict-system` records the explicit functor in
`Sheaf.Paper.SemilinearOrdinarySourceStrictSystem`, with its proved identity, composition,
and functor laws. This is a completed construction, with zero holes. Its exact evaluation
and transition choices are needed before applying an arbitrary `I n.modules`; the existing
sequence-site equivalence instead uses its own coefficient-map presentation. There is no
new unproved obligation and no change record is needed for a new module.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
