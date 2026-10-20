## What changed

Retired Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreExistence in favor
of WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationCoreExistence,
as assigned by coord/queue.tsv and coord/retire-items.tsv. Reattached
compatible-strict-henselization-core-existence to the existing upstream theorem.
Also retired Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreCompletion,
whose sole consumer is the same CoreData proof, and reattached its node to its
proved upstream twin. No Lean importer remains for either copy after adaptation.
The upstream public declaration and its complete proof are unchanged.

Adapted its only direct consumer,
Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreData, retaining the
consumer theorem's exact statement. Its proof privately imports upstream core
existence and core completion, composes their spectrum presentations with the
canonical small-to-large colimit comparison, and transports the structural
square and the two residue factorizations. The comparison's base-map equation
is proved from the colimit injection formula and the two cone-leg equations.
Its structural-map public import now names the upstream small-colimit module,
which preserves the objects appearing in its public statement while avoiding
the duplicate helper declaration. Updated its node's proof route accordingly.

Validation: lcompile.py compiled CoreData, then the unchanged
ProjectiveLineCompatibleStrictHenselizationResiduesCore and
ProjectiveLineCompatibleStrictHenselizationResidues against its rebuilt artifact,
with no errors or warnings (3.0, 2.7 and 2.7 seconds respectively). Both proposed
upstream proof imports pass tools/import_direction.py. The downstream files were
used only for validation and are not changed in the delivery.

Change record: coord/changes/F1-retire-compatible-strict-henselization-core-existence.md.

## Proved and sorry left

The item and the retired completion copy had zero holes and have zero holes after retirement. Holes closed: none.
Holes added: none. No theorem was split off.

AlgebraicGeometry.Etale.exists_compatibleStrictHenselizationCoreExistence retains
its complete upstream proof. The adapted
AlgebraicGeometry.Etale.exists_compatibleStrictHenselizationCoreData has a complete
proof. Its new private localizationComparison_base and automatically generated
reassociated theorem are proved; localizationComparison is a concrete spectrum
isomorphism. No sorry remains in any delivered Lean file.

## No longer needed

Pruned modules: Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreExistence
and Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreCompletion.
CoreData replaces its private import by the upstream twin, and also replaces
its private Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreCompletion
import by the upstream twin. Its public Sheaf strict-henselization structural-map
import is replaced by the upstream module defining the same small-colimit map.

The retired file's Sheaf.Paper.StrictHenselizationFunctoriality proof import and
its four private embedding/residue helpers are no longer part of this consumer's
proof. Their mathematical work is already present in the unchanged upstream
existence proof. None of their mathematical nodes is withdrawn, and no claim is
made that these modules are globally unused by other consumers. The existence,
completion, strict-henselization-limit and structural-map nodes remain needed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an open hole and earlier decompositions, but
the current item is an already proved, zero-hole retirement assignment. A direct
import replacement is insufficient: the upstream theorem uses strictLocalization
and strictLocalizationToBase, while the consumer still states its result using
strictHenselizationScheme and strictHenselizationStructuralMap. Transport through
the canonical colimit isomorphism is necessary to preserve that statement.

The original item fails to import against the published build with: import
WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension failed, environment
already contains AlgebraicGeometry.Scheme.smallStrictHenselizationColimitIso from
Sheaf.AlgebraicGeometry.StrictHenselization. This packet uses the upstream proof
route and passes compilation, including the two unchanged transitive consumers.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
