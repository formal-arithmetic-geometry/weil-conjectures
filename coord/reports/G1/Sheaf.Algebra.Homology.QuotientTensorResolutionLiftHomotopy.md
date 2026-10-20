## What changed

Retired Sheaf.Algebra.Homology.QuotientTensorResolutionLiftHomotopy, as assigned
by coord/queue.tsv (kind retire) and coord/retire-items.tsv. The old module is
listed in deleted.txt and has no remaining live importer in the delivered set.

SelfTorOrdinaryResolutionSections now imports the upstream twin, which proves
the same quotient_tensor_resolution_lift_homotopy statement. The upstream file
is unchanged. The public generic augmented_lift_homotopy theorem is absent
from the upstream API (its version is private), so its existing signature,
docstring, and complete proof are preserved verbatim in the new module
Sheaf.Algebra.Homology.AugmentedResolutionLiftHomotopy. The only generic caller,
ResolutionInflationComparison, now imports that module. Both consumer edits
are single proof-import replacements; their statements and proofs are unchanged.

Updated the two existing DAG attachments to their new providers. The quotient
node describes the upstream private lifting induction rather than a use of
the now separate public helper. No new mathematical statement or node is added.

Validation: lcompile.py --all compiled the generic helper in 1.5 s,
SelfTorOrdinaryResolutionSections in 11.8 s, and ResolutionInflationComparison
in 21.0 s, all with exit code 0. A literal extraction check verified the moved
helper's entire declaration and the quotient theorem's upstream signature.
Both consumer diffs consist of one proof-import replacement each. The change
record lists all 13 live downstream consumers and the three absent inventory
entries. No module in the packet imports the withdrawn module.

Change record: coord/changes/retire-quotient-tensor-resolution-lift-homotopy.md.

## Proved and sorry left

This is a zero-hole retirement repair: the assigned module had 0 sorries.
Holes closed: none (0). Holes added: none (0). Split off: none (0).
No sorry remains in any delivered Lean file.

Preserved the complete proof of ModuleCat.augmented_lift_homotopy
(node new-t4-augmented-resolution-lift-homotopy) in its new module.
ModuleCat.quotient_tensor_resolution_lift_homotopy
(node new-h2-quotient-tensor-resolution-lift-homotopy) is now supplied by its
already proved upstream declaration, with identical binders and conclusion.
Both adapted callers remain completely proved.

## No longer needed

The duplicate module Sheaf.Algebra.Homology.QuotientTensorResolutionLiftHomotopy
and both live imports of it are withdrawn. Its private prevD_chain,
quotientTensorLift, and quotientTensorLift_tmul copies are removed; the upstream
proof retains its own existing versions. The quotient node no longer depends
on the public generic-helper node, because its upstream proof uses its own
private induction. The generic node remains needed by ResolutionInflationComparison.

The new generic module requires only
Mathlib.CategoryTheory.Abelian.Projective.Resolution. The old quotient-specific
imports of ModuleCat.ChangeOfRings, ModuleCat.Monoidal.Basic,
Ideal.Quotient.Defs, and ModuleCat.Abelian are unnecessary for the generic theorem;
the upstream quotient module still supplies the imports needed by its caller.

Three consumers in the retirement inventory are already absent from the live
library: DerivedSelfTorAffineCoordinates, SelfTorAmbientSectionCoordinates,
and SelfTorNonpositiveFlatSections. Their upstream twins already import the
upstream homotopy module. No live mathematical result is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 proof brief did not identify the current retirement assignment.
The module already compiles with zero holes. coord/queue.tsv and the human's
retirement hand-off in coord/changes/retire-sheaf-twins-20261020.md identify the
required repair. The retirement inventory describes the APIs as the same,
but the upstream augmented_lift_homotopy helper is private, while the Sheaf
version is public and used by the representation caller. Blindly replacing
both imports with the twin would lose that theorem. Relocating the existing
proved generic theorem preserves its API without editing the source library.

Searches run with msearch.py: LeanFinder for augmented projective-resolution
homotopy uniqueness, Loogle for liftHomotopy, and grep for liftHomotopy,
prevD_chainComplex, and quotient_tensor_resolution_lift_homotopy. Mathlib's
ProjectiveResolution.liftHomotopy requires a projective resolution as target;
it does not replace the generic helper with an arbitrary exact target.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
