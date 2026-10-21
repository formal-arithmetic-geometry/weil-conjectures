## What changed

Restored lean/Sheaf/Paper/BoundedConstructiblePushforwardRestriction.lean verbatim
from its assigned quarantine source. The live file was absent following the
cluster restore recorded in coord/rework.tsv. This is a source restoration,
not a proof closure or a rebase of an existing live module.

The four restored declarations in AlgebraicGeometry.ProEtale.CondensedRing are:
PreservesBoundedConstructiblePushforwards,
boundedConstructibleLowerStarOfPreserves,
boundedConstructibleLowerStarOfPreservesCompatibility, and
boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves.
The predicate quantifies over all morphisms between separated finite-type
k-schemes. The functor uses ObjectProperty.lift on the actual ambient derived
pushforward; its compatibility is liftCompιIso. The adjunction is the ambient
adjunction restricted using Mathlib Adjunction.restrictFullyFaithful. All data
are constructed; there is no arbitrary witness or fresh derived functor.

The sole public import remains the complete existing BoundedConstructible
module. Its existing restricted operations and coefficient cases stay exported.
The node sk-def-sfb-dc-restricted-functors and its Lean attachment, statement,
proof, dependencies and unit route are preserved unchanged. No new node or
forced adaptation is needed.

Validation: restored module compiled cleanly alone through lcompile.py (3.9 s).
A second compilation in import order compiled the module (5.2 s) and the
unchanged archived Sheaf.Paper.BoundedConstructibleBaseChange consumer (4.4 s).
The consumer copy was removed from the delivery after checking. Its unit and
counit uses verify that the restored adjunction retains its expected interface.
The delivery tool performs the separate declaration/axiom probe and preflight.

LeanFinder and Loogle searches confirmed ObjectProperty.lift and
Adjunction.restrictFullyFaithful as the existing generic constructions. Their
Mathlib sources were read, together with the blueprint unit and proof. The
original construction already uses these; no alternative construction is needed.
Zero objects, empty schemes where morphisms exist, and identity morphisms cause
no extra assumptions: the lift simply attaches H f K to the ambient image.
The conditional hypothesis remains explicit for arbitrary coefficients; this
delivery asserts no unconditional constructibility theorem for such coefficients.

Change record: coord/changes/E3-restore-bounded-constructible-pushforward-restriction.md.

## Proved and sorry left

Zero of zero original holes closed; zero holes added; zero split off; zero
sorry declarations remain in this module. All four restored declarations have
complete definition bodies. Imported unfinished results are not newly proved
by this restoration. The assigned repair is restoring the missing definitions,
not reducing a theorem's axiom closure.

## No longer needed

None. No import, declaration, node, module or dependency was pruned. In
particular the quarantined base-change consumer still needs this interface,
and the sk-def-sfb-dc-restricted-functors unit and its dependencies stay intact.
The archived file is preserved; no deleted.txt is used.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean/ because of the recorded cluster restore; its
quarantine archive is complete and already compiles against the current build.
No Lean source defect was reproduced, so a speculative definition change would
be unjustified. The necessary repair is the verbatim restoration itself.
The DAG attachment is accurate and is not cleared or rebound.

The downstream.py check requires --allow-missing for the absent live module;
it reports zero live importers. The archive search finds four retained
consumers, listed in the change record. These were checked separately rather
than interpreting the live importer count as authorization to withdraw.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
