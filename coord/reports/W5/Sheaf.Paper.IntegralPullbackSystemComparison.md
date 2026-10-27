## What changed

Constructed `WeilConjectures.integralPullbackSystemComparison` from the existing
normalized realization and effective quotient descent interfaces. The selected
calculi are exactly the ones used by `integralSystemReduction`. Coherent
reduction of realization followed by the whole-system counit gives the natural
system map; effectivity proves its components invertible. The recorded finite
counit projection identity proves the normalization for every representative
and quotient level. The theorem signature and the body of
`integralSystemPullbackReductionIso` are unchanged.

Repaired the reversed higher import in `IntegralComparisonSequenceSystems`,
retaining its complete lower public closure, including smallness and ringed-site
duality interfaces. Only the two higher comparison/composition modules cease to
be reexported; neither declares a global instance or changes a global instance
attribute. The direct consumer mentioning the system comparison,
`AutomorphismConstructibleStageEquivalence`, imports both higher modules itself.
The inventory and current holders are in
`coord/changes/W5-sequence-comparison-import-direction.md`.

Reviewer correction (2026-10-26): the delivered packet also aliased the four
sequence constructions (base change, ring component, ring map, direct image) to
their ambient implementations and rewrote 17 private proofs of the sequence
module. Those changes were not forced, and they broke the unchanged
`CompletedComparisonQuotientRealizationDefs` (its `unfold … integralComparisonSequenceDirectImage; rw [hr]`
no longer closes). The landed sequence module is the published one with only
the import block changed. It compiles, and so do the item, the restored
projection and all direct importers that compile against the published build.

The unchanged `FiniteCounitRestrictionTowers` consumer compiled in 51.7 seconds,
and the three additional definitional-equality checks compiled in 42.0 seconds
(result `739064c424a03477dd7835d5`). Temporary test sources were removed.
The public visibility audit of 32 current module/owner pairs found no lost
access. The completed import graph is acyclic with no missing source. No
profiling commands, diagnostic declarations, or raised heartbeat budget remain.
The delivery checks compile the final packet again.

## Proved and sorry left

Closed the item's one original hole:
`WeilConjectures.integralPullbackSystemComparison`, node
`lem-pod-integral-pullback-system-comparison`.

Restored one existing lower hole:
`WeilConjectures.integralPullbackCounitProjection`, node
`lem-pod-integral-pullback-counit-projection`, with its exact recorded signature.
It is the finite map calculation and asserts neither existence nor invertibility
of the system comparison. Relative to the live source this is one upper hole
closed and one lower hole restored: net zero, a decomposition repair. Relative
to C4's recorded split it adds no mathematical obligation, name or node.
The item and sequence module have zero holes; the restored projection has one.
No hole is in a definition or private helper.

The whole-system counit clause covers zero objects and empty schemes. The
coefficient exponent remains `n + 1`, including exponent one at `n = 0`.
No bound, additional hypothesis or representative restriction is introduced.

## No longer needed

Removed proof imports `Sheaf.CategoryTheory.StrictRoosComparison` and
`Sheaf.Paper.NormalizedDVREffectivity` from the item. Their work is encapsulated
by normalized realization, effectivity and the finite projection interface;
their modules remain needed transitively, so no withdrawal is claimed.

Removed the higher public import `Sheaf.Paper.IntegralPullbackComposition` from
the sequence module to break the cycle. The composition theorem remains a
consumer of the item and is not pruned. All eight declared dependency modules
remain used. The full-faithfulness theorem itself is not invoked: its module
supplies reduction, its chosen calculus and the evaluation isomorphisms.
No unit statement or unit proof step is bypassed. No Lean module or DAG node is
withdrawn, and no new node is added.

The restored projection imports `IntegralOperationsPreserveConstructible`
directly for its finite comparison statement, without reexporting the broader
`DerivedPullbackTensorHom` interface.

## Where the brief, the DAG or earlier work was wrong

The C4 packet was reverted after its import repair dropped lower public
interfaces, breaking `FiniteCounitRestrictionTowers` with unresolved
`EssentiallySmall` universes. This packet preserves those interfaces and checks
that original consumer.

The finite projection node retained its attachment after its source was removed
with the C4 reversion. V8's claim was released at 2026-10-25T22:30:40Z as
"done meanwhile" (coord/deliveries.log), although no file was present. There is
no quarantine/rework row or current holder. This packet restores exactly that
existing statement and proof plan, including its node copy for registration.
It creates no duplicate node or renamed upper obligation. The restoration record
is `coord/changes/W5-restore-integral-pullback-counit-projection.md`.

An existing transitive dependency, `primitiveQuotientRealizationComparisons`, is
already marked `STATEMENT-DISPUTED`: its all-presentation limit equation asks
finite derived evaluations to detect equality of morphisms. This packet uses
the stated normalized-model interfaces and does not repair that lower issue.
Their representative normalization still needs correction before the transitive
proof is complete.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
