## What changed

Proved `Module.localization_commutes_with_embedded_point_removal` in
`Sheaf.RingTheory.LocalizationEmbeddedPoints`, with its signature unchanged.
All ten private support, topology and localization helpers are proved.
The argument lifts a localized submodule to an inverse-image submodule D, replaces
D by f^n D so localization is injective, and compares annihilators to identify
support with the closure of the localized support. This proves equality of the
two maximal submodules. Mathlib's canonical localization–quotient equivalence
then gives the required equivalence and its formula on quotient classes.

Updated the existing node's proof, proof_deps and proof_origin to this argument.
The import change is recorded in
`coord/changes/localization-embedded-points-imports.md`, including all ten
transitive consumer modules from tools/downstream.py.
Replaced the public import of `Sheaf.RingTheory.RemoveEmbeddedPrimes` by the
Mathlib modules actually needed for the unchanged public statement:
`Mathlib.RingTheory.Support`, `Mathlib.RingTheory.Spectrum.Prime.Topology` and
`Mathlib.Topology.GDelta.Basic`. The additional proof imports are
`Mathlib.Topology.LocalAtTarget` and `Mathlib.RingTheory.Localization.Submodule`.
Validation: the final module compiled without errors or warnings in 13 seconds
through lcompile.py. A temporary `#print axioms` check reported exactly
`propext`, `Classical.choice`, `Quot.sound`; the check command was then removed.
The old and new public theorem signatures were compared verbatim and are equal.

No definitions, instances, or public signatures change. The sole direct consumer,
`Sheaf.AlgebraicGeometry.RemoveEmbeddedPoints`, independently imports
`Sheaf.RingTheory.RemoveEmbeddedPrimes` already; no consumer adaptation is needed.

The unit record has no realized statement or proof steps. This is a proof of the
existing localization node in the Hilbert-polynomial route, with no unit bypass.
The proof handles f=0, f=1, nilpotent f, zero M and the zero ring without nonzero
or nontriviality assumptions: kernel stabilization and empty-support topology
apply to those cases as stated.

## Proved and sorry left

Closed the one existing hole:
`Module.localization_commutes_with_embedded_point_removal`
(node `lem-sc-hilbert-embedded-points-affine-localization`).
There are zero sorries left in the item and zero added elsewhere. No split-off
statements, new public declarations, or new modules were added.

## No longer needed

Removed import `Sheaf.RingTheory.RemoveEmbeddedPrimes`; its theorem
`Module.exists_maximal_nowhereDense_support_quotient` and node
`lem-sc-hilbert-embedded-points-affine-removal` are not proof dependencies of this
localization theorem, since K and Kf and their maximality are hypotheses.
The conceptual statement dependency is retained. The removal module is still
needed independently by `Sheaf.AlgebraicGeometry.RemoveEmbeddedPoints`; no module
is withdrawn or claimed globally pruned.

The old plan's generic-point kernels, finite products of localizations, and
Artinian/nilpotence argument at the minimal support primes are unnecessary.
Only Mathlib declarations occur in the actual proof dependencies.
Removed exploratory redundant proof imports
`Mathlib.RingTheory.Spectrum.Prime.Module` and `Mathlib.RingTheory.Noetherian.Defs`.

## Where the brief, the DAG or earlier work was wrong

The listed affine-removal theorem states existence and quotient properties; it
does not give the generic-kernel characterization that the old localization plan
needed. It supplies no additional premise beyond this theorem's existing
maximality hypotheses. The full replacement proof uses kernel stabilization and
support closures instead. Stacks Tag 02M7 itself omits the proof; the new proof is
explicitly recorded as agent-written. The mathematical statement is unchanged.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
