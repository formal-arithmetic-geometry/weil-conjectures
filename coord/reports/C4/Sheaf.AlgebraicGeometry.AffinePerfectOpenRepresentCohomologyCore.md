## What changed

Retired Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyCore in favor of
WeilConjectures.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyCore, under the
human-approved hand-off in coord/changes/retire-sheaf-twins-20261020.md and the item's
DIFFERENT retirement row. deleted.txt withdraws the duplicate; the existing node
lem-sc-affine-perfect-open-represent-cohomology-core now points at the official file.
No source-library file, definition, target statement or consumer is edited.

The exact signature comparison shows that upstream removes only the unused
E : schemeDerivedQCohCategory (Spec (.of A)) parameter. All other binders and all
three conclusions agree. A scratch theorem retaining the entire old signature is
proved by exact affine_perfect_open_represent_cohomology_core A r f. It compiles on
the server in 1.9 seconds. Its axioms, the official core theorem's axioms, and both
consumer theorems' axioms are exactly propext, Classical.choice and Quot.sound.

Both official consumer modules were copied unchanged into the item's scratchpad
and compiled independently through lcompile.py: the colimit module in 22.5 seconds
and the represent-cohomology module in 6.6 seconds. The scratch interface imports
both consumers and the official core, so that environment is checked together.
No scratch file is part of the delivery.

The change record is
coord/changes/C4-retire-affine-perfect-open-represent-cohomology-core.md.

## Proved and sorry left

This is a zero-hole duplicate retirement: 0 of 0 original sorries closed,
0 sorries added, 0 split off, and no sorries left in the delivered code.
AlgebraicGeometry.affine_perfect_open_represent_cohomology_core already has a
complete official proof; its permitted axioms were checked recursively.
No new proof progress or decomposition is claimed.

## No longer needed

Withdrawn module:
Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyCore.
Its two proved private helpers boundary_zero and chain_augmentation_compatibility
are redundant with the official proof and have no external users.

The withdrawn file's imports are no longer needed through that file:
WeilConjectures.AlgebraicGeometry.KoszulOpenSystem,
WeilConjectures.AlgebraicGeometry.PerfectComplex,
WeilConjectures.AlgebraicGeometry.KoszulOpenConeComparison, and
Sheaf.Paper.AffinePerfectKoszulPrincipalUnit.
The corresponding mathematical dependencies remain needed by the official proof;
no dependency node or upstream declaration is pruned.

tools/downstream.py reports zero modules downstream of the Sheaf copy; its only
name-use hit is its own declaration. Source searches also find no import of the
retired module in lean/ or quarantine/.
The inventory's former Sheaf consumers AffinePerfectOpenRepresentCohomology and
AffinePerfectOpenRepresentCohomologyColimit are already absent. Their live official
counterparts already import the upstream core and omit the E argument.
The DAG parent lem-sc-affine-perfect-open-represent-cohomology-colimit still needs
the same core node; its replacement realization is the official theorem, not an
abandonment of that dependency. The unit sk-thm-picard-duality has no realization
entry for this node. Its route and all node proof dependencies are preserved.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an unfinished theorem, but this assigned item
is an approved retirement with zero existing holes. Its inventory's consumer list
predates the consumers' own retirement. Its DIFFERENT classification records only
the now-unused E binder, not a change to the structural conjunction. The old node's
Lean attachment still pointed at the duplicate and is corrected in this packet.

The upstream proof and the old proof follow the same cone-comparison, perfectness,
and augmentation-compatibility argument. Searches through msearch.py returned no
exact Mathlib match (LeanFinder gave general distinguished-triangle results,
Loogle did not know this project declaration, and grep returned no hit); direct
source search found the exact, already proved official replacement. No new lemma,
mathematical statement repair, or new node is necessary.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
