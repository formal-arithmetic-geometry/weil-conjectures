## What changed

Completed `AlgebraicGeometry.Scheme.proEtalePullbackStalkCoherence` in
`Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence`. The existing statements,
definition bodies, and previously completed proofs are preserved. All eight
conjuncts follow from normalized colimit germs and generic exact-derived coherence.

Added the proved ordinary-comparison characterization
`proEtaleConstantRingPullbackComposition_ordinary` in
`Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence`. Its unit-section
formula identifies the stalk calculation, and its derived equation identifies
that calculation with the prescribed canonical compositor. Added the fully proved
specialization `proEtaleConstantRingPullback_underlyingUnit_isIso` of the existing
private `ringUnitComparison`. The item uses this public statement and drops its
`import all` of the adjunction module, keeping the implementation details private.

In `Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`, marked the
existing compositor `@[no_expose]` and added a proved equation with its identical
defining formula. The coherence file uses that equation at its existing unfolding
site. This avoids unfolding nested uniquely normalized witnesses. The definition
body, mathematical data, public imports, and all existing signatures are unchanged.
The change record is `coord/changes/G8-proetale-compositor-characterization.md`.

Repaired return ea464a5a68: omitted the ancillary `Sheaf.Paper.IteratedWeilMap`
restoration from this packet. The current tree quarantines that module and all
three unavailable imports named in the return. This delivery neither restores nor
withdraws those modules and changes none of their quarantine files, node
attachments, or dependencies. Its previous consumer optimization is retained only
as sandbox scratch work; it is not a change to the current library. No path is
listed in `deleted.txt`.

The retained proof and node updates remain. The packet contains the three
algebraic-geometry modules and the forced adaptation of their unclaimed consumer. Attempts to
retain the compositor's original exported body and use only local irreducibility
compiled the derived-coherence module but timed out in the stalk module, including
a diagnostic with the final theorem omitted. The defining-equation interface is
therefore retained. The additional underlying-unit interface removes the private
implementation import that made the early stalk construction expensive. The full
item compiled in 39.4 seconds. All four delivered files compile without warnings;
the five current unchanged consumer probes (DirectImageScalarExchange,
FiniteSystemPullbackCoherence, IntegralFinitePullbackComposition,
PullbackCoefficientIterateCoherence, TateInverseLimitBaseChange) also passed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.proEtalePullbackStalkCoherence`
(node `lem-trf-proetale-pullback-stalk-coherence`). All eight conjuncts are proved.

Holes closed: 1. Holes added: 0. Sorries left in the four delivered modules: 0.
No intermediate theorem is split off. The three new API theorems,
`AlgebraicGeometry.Scheme.proEtaleConstantRingPullbackComposition_eq` and
`AlgebraicGeometry.Scheme.proEtaleConstantRingPullbackComposition_ordinary`, and
`AlgebraicGeometry.Scheme.proEtaleConstantRingPullback_underlyingUnit_isIso`,
are fully proved.

## No longer needed

Removed the private import `Sheaf.Paper.IntegralFinitePullbackComposition` from
the item: its proof uses ordinary finite-coefficient exact functors. Also removed
`import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`: the public
constant-coefficient unit-comparison specialization replaces its private lemma.
The generic
fibre-product and derived coherence lemmas it needs are imported directly.
No module is withdrawn, no existing DAG dependency is pruned merely because its
source is quarantined, and the blueprint unit route is preserved.

The ancillary IteratedWeilMap restoration and its separate change record are
omitted from the packet; this is not mathematical pruning of that module or any
of its dependencies.

## Where the brief, the DAG or earlier work was wrong

The returned packet tried to restore an additional consumer whose three public
imports have no current source in `lean/`. The rework rows preserve all four
modules in quarantine. Compiled artifacts from an earlier build are insufficient
to authorize their restoration without those source dependencies. This repair
keeps those quarantined modules untouched and adapts only the current consumer
that is forced by the compositor interface change.

The proof plan is mathematically sound. The existing normalized comparison API
identifies the derived comparison on complexes without new K-flat calculations
or an unfinished intermediate result.

## Forced adaptations

`Sheaf.AlgebraicGeometry.ProEtaleConstantModuleComparisonLocalization` is
unclaimed. Against the delivered compositor module, its original source failed
with `failed to set reducibility status, proEtaleConstantRingPullbackComposition
is not a definition` at the local irreducibility attribute, and with `Tactic
unfold failed to unfold proEtaleConstantRingPullbackComposition` at the explicit
unfolding in `constantData`. The adapted source removes that one name from the
local irreducibility attribute and replaces the unfolding with
`rw [proEtaleConstantRingPullbackComposition_eq]`; its declaration signatures
and all other lines are unchanged. The adapted file compiles.

## Second reading by G8

Repair reread: the item theorem and its three supporting algebraic-geometry
modules compile with no sorries, and the forced consumer adaptation preserves
its existing declarations and proof route. The change record lists every
computed compositor user, including this consumer.
