## What changed

Retired `Sheaf.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties`, listed
as a retirement item in `coord/retire-items.tsv`. Its theorem is already completely
proved with the identical signature in
`WeilConjectures.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties`.
The only extra declaration, `AlgebraicGeometry.restriction_additive`, duplicates
an upstream instance in `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`.

Migrated the private proof imports in `NestedOpenSingleDirectImageComparison`,
`PicardAffineStructureModelTransport`, and `SelfExtTorResolutionLocal`, replacing
four named additive-instance calls by `inferInstance`. These were the three live
direct consumers and were unclaimed. Their signatures and public imports are unchanged.
Repointed `lem-pc-open-immersion-restriction-derived-properties` to the upstream
module and removed the retired helper from its auxiliary-declaration list.
No upstream module, definition, or target statement changes.

Change record: `coord/changes/G9-open-immersion-restriction-retirement.md`.

Validation: all three adapted consumers compile cleanly with lcompile.py
(19.9 s, 48.5 s, 6.2 s). The unchanged indirect consumer
`SelfExtTorResolutionModel` compiles against the sandbox overlay (15.3 s).
The delivery parser reports no changed signature and no before/after sorries
in any adapted consumer. A separate compiled check synthesizes restriction
additivity and applies the upstream theorem unchanged. `#print axioms` for
that theorem lists exactly `propext`, `Classical.choice`, and `Quot.sound`.

The required dry run passed: commit `9aaff2e857a`, review class CODEX.
Its note says the appended probe for `NestedOpenSingleDirectImageComparison`
timed out at 60 s; the source file itself had compiled cleanly in 19.9 s.
The delivery tool leaves that additional probe for the merge to repeat.

## Proved and sorry left

This is a zero-hole retirement repair: the original item contains zero sorries.
Zero holes closed, zero holes added, zero split off. The three adapted consumer
modules also contain zero sorries, and no definition is hollowed.
`AlgebraicGeometry.openImmersion_restriction_derived_properties` is retained through
its existing proved upstream declaration, with the same unrestricted open-immersion
statement. `AlgebraicGeometry.restriction_additive` is retired in favour of the
existing inferred additive instance, whose map_add proof is rfl.

## No longer needed

Pruned the duplicate module
`Sheaf.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties` and its three
live import edges. The duplicate theorem proof and the redundant named additive
instance are no longer needed. Each live consumer now imports the upstream twin.

The original module's public imports `Mathlib.AlgebraicGeometry.Modules.Sheaf` and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`, and its
proof imports `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`,
`WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful`,
and `Mathlib.AlgebraicGeometry.Restrict` are supplied by the upstream theorem's
module as needed. No claim is made to prune these modules themselves: the upstream
proof uses the same finite-limit and K-injective restriction arguments.
All five DAG parents continue to cite the same node, now attached upstream.
No mathematical dependency or unit proof step is pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief does not identify that this zero-sorry module is a
retirement item. The current retirement table and human-approved hand-off provide
the assignment. The table correctly says that the twin lacks the named helper,
but upstream already has the corresponding additive instance; no replacement
lemma or new node is necessary.

Read the theorem's DAG proof and all three declared dependencies, the upstream
proof, the upstream additive instance, Stacks cohomology.tex
lemma-restrict-K-injective-to-open (08BS), and modules.tex lemma-limits-colimits
(01AH). The upstream theorem retains the sectionwise finite-limit proof and the
image-open factorization for K-injective restriction, including empty opens.
Mathlib searches through msearch.py used LeanFinder, Loogle and grep. The existing
upstream theorem is the direct complete match; no new mathematical argument is required.

The retirement table names five historical consumers. Two are quarantined:
`PerfectHomOpenMateResolutionNormalization` and
`PicardAffineStructureProjectiveRepresentation`. Their archives and rework rows
are preserved. Their DAG theorem dependency remains valid; the change record
specifies the import and instance-call migration needed on restoration. The three
remaining consumers are all live direct importers and are migrated in this packet.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
