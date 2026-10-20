## What changed

Retire Sheaf.RingTheory.BoundedProjectiveResolutionDimension under the human's
Hand-off in coord/changes/retire-sheaf-twins-20261020.md. The current copy is an
empty public reexport of the proved official twin. deleted.txt withdraws the
copy; no public declaration, definition, upstream source or target statement is
changed. There is no active Lean importer of the copy to adapt.

The node lem-weil-pbc-projective-resolution-ext-degree already points to
WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension and
ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE. Refresh only
lean.note to record the retirement. All seven parent nodes, including the two
quarantined parents, continue using that same node and theorem. Its statement,
proof, proof dependencies and sk-thm-p1 unit route remain unchanged.

The historical consumers AffinePolynomialResolutionOfStalkwise,
ProjectiveResolutionExtAllDegrees and ProjectiveResolutionExtCharacterization
have already moved to their official modules, which directly import the twin.
The other two historical consumers, AuslanderBuchsbaum and
UniformPerfectQuotientBound, are preserved as quarantine archives with separate
rework assignments. They are not active compiled modules. Preserve their Lean
attachments and obligations; the change record gives their exact private-import
replacement when restored. Their unrelated existing API repairs are not part of
this zero-declaration retirement. No archive is edited or withdrawn.

Change record: coord/changes/C1-retire-bounded-projective-resolution-dimension.md.

## Proved and sorry left

Original direct holes: zero. Holes closed: zero. Holes added: zero. Holes left
in the withdrawn item: zero. Split-off statements: zero. This is a retirement,
not a new proof or a decomposition. No existing theorem proof is weakened.

The official ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE,
ModuleCat.exists_hasProjectiveResolutionLE_iff,
ModuleCat.projectiveDimension_eq_of_hasProjectiveResolutionLE and
Ring.hasGlobalDimensionLE_iff retain their complete proofs. A server-compiled
probe checks the bridge signature and all four declarations' axioms: only
propext, Classical.choice and Quot.sound occur (1.0 second).

All ten current direct users of the official bridge compiled unchanged through
lcompile.py, each in 1.0--2.4 seconds with no diagnostics:
Sheaf.Algebra.ProjectiveDimensionWellDefined,
Sheaf.RingTheory.ProjectiveDimensionSESKernel,
WeilConjectures.AlgebraicGeometry.AffinePolynomialResolutionOfStalkwise, and
WeilConjectures.RingTheory.{CyclicGlobalDimension, LocalizationFiniteGlobalDimension,
ProjectiveResolutionExtAllDegrees, ProjectiveResolutionExtCharacterization,
ResidueFieldProjectiveDimension, ResidueFieldProjectiveDimensionDepth,
GlobalDimensionFiniteModules}. Validation sources are outside the packet's lean/
root, under scratchpad/validation, and are not delivered.

## No longer needed

Pruned module: Sheaf.RingTheory.BoundedProjectiveResolutionDimension. Its only
import, public import WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension,
is removed with the copy. All active consumers already import the official twin;
there are no import or declaration-name rewrites left in the active library.
The excluded validation probe now imports the official twin as well.

No mathematical DAG node is pruned. In particular,
lem-weil-pbc-projective-resolution-ext-degree, its bounded-resolution construction,
its successor-splicing dependency and all seven parent edges remain needed.
The quarantine archives and their outstanding repair nodes are preserved.

## Where the brief, the DAG or earlier work was wrong

The retained earlier packet treated this as a stale proof assignment, because
E2 had already restored the zero-hole reexport at landing
20261020T152957-L-2857871. Its required initial dry run was rejected because the
item was unchanged. The current explicit RETIRE assignment supersedes keeping
that redundant path, so this packet performs the requested deletion instead.

The retirement TSV describes an older source snapshot: three listed consumers
are now official modules, the other two are quarantined, and the listed DAG
attachment already points upstream. Live-source and quarantine scans distinguish
these cases; absence from lean/ is not used to withdraw a quarantined obligation.
There is no mathematical statement dispute and no change to a definition.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
