## What changed

Completed the zero-sorry retirement repair listed in `coord/retire-items.tsv`.
Withdrew `Sheaf.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties`:
the identical theorem already has a complete proof in its upstream twin, and
the helper `AlgebraicGeometry.restriction_additive` duplicates the additive
instance in `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`.

Changed only the private import and four helper applications in the three live
consumers `NestedOpenSingleDirectImageComparison`,
`PicardAffineStructureModelTransport`, and `SelfExtTorResolutionLocal`.
They now import the upstream theorem and infer the existing additive instances.
All existing consumer signatures, visibility and public imports are unchanged.
Updated the node's Lean attachment to the upstream module and removed the
retired helper from its auxiliary declaration list.

Change record: `coord/changes/A4-open-immersion-restriction-retirement.md`.

Validation: all three adapted consumers compile cleanly via `lcompile.py`
(14.7 s, 31.3 s and 3.6 s). A separate compiled check applies the identical
upstream theorem, synthesizes restriction additivity and prints exactly
`propext`, `Classical.choice`, `Quot.sound` as the theorem's axioms.

## Proved and sorry left

The assigned module originally has zero sorries. This is a retirement repair:
zero holes closed, zero holes added, zero split off. No sorry remains in the
item or any of the three adapted modules. No definition is hollowed.

`AlgebraicGeometry.openImmersion_restriction_derived_properties` remains proved
by the existing upstream declaration with its unchanged signature.
`AlgebraicGeometry.restriction_additive` is retired in favor of the existing
upstream additive instance, whose map_add field is proved by rfl.

## No longer needed

Pruned the duplicate module
`Sheaf.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties` and its
three live direct import edges. The four explicit applications of its redundant
`restriction_additive` helper are no longer needed.

The withdrawn module's public imports were
`Mathlib.AlgebraicGeometry.Modules.Sheaf` and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`;
its proof imports were
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`,
`WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful`,
and `Mathlib.AlgebraicGeometry.Restrict`.
Their required declarations remain supplied through the upstream theorem's
module. These dependencies are not claimed pruned: its proof still uses them.

No mathematical node or unit step is pruned. All five DAG parents retain the
same node dependency, now attached to the upstream proof. Both quarantined
consumers keep their archives, rework rows and mathematical dependencies.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief does not say that this zero-sorry module is a
retirement item; the current queue and retirement table identify that repair.
The table correctly identifies the helper absent from the upstream twin,
but the existing upstream additive instance makes a replacement unnecessary.

Read the node's plan, the three dependency declarations, the unchanged upstream
proof, Stacks cohomology.tex lemma-restrict-K-injective-to-open (08BS), and
modules.tex lemma-limits-colimits (01AH). The proof retains sectionwise limits,
the image-open factorization and K-injective preservation by exact extension
by zero; the argument includes the empty open. No hypothesis is changed.
Required msearch.py searches used LeanFinder, Loogle and grep; local rg found
the exact upstream theorem and additive instance.

The earlier G9 retirement adapted the three then-live direct consumers. During
this session the shared maintainer tree briefly restored
`PerfectHomOpenMateResolutionNormalization`, then quarantined it again while
recovering the red batch. The final packet is reconciled with the current tree:
three live direct consumers are adapted and both quarantined archives remain
untouched, with the required restoration migration recorded in the change record.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
