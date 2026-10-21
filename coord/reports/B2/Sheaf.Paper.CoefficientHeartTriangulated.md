## What changed

Restored `lean/Sheaf/Paper/CoefficientHeartTriangulated.lean` verbatim from its
quarantine source, as assigned by the rework row dated 2026-10-20. This reinstates
`AlgebraicGeometry.ProEtale.constantModelBoundedConstructible_field_triangulated`
and its two proved private helpers. The public interface, imports, source
references, existing DAG attachment and existing mathematical proof are preserved.
Change record: `coord/changes/B2-coefficient-heart-triangulated-restoration.md`.

The restored module compiles cleanly through the required lcompile.py service in
5.2 seconds. Read the existing coefficient-heart closure, well-definedness and
weak-Serre cohomology signatures against each application. The proof retains the
unit's cohomology cone argument through the generic weak-Serre theorem; the
complementary-idempotent kernel argument supplies retract closure. Zero objects,
rank zero, the empty scheme and both coefficient choices remain covered.

## Proved and sorry left

The archived source already has zero holes. Holes closed in this session: zero.
Holes added: zero. Holes split off: zero. Holes remaining in the restored item:
zero. Its public theorem and both private helpers are fully proved from existing
library declarations. Restoration does not claim to close any holes in those
dependencies or count the earlier worker's proof as new progress.

## No longer needed

None in this restoration. Both public imports and all three proof imports are
retained. No node, module, declaration, dependency, archive or Lean attachment is
withdrawn. The existing node's proof already matches the restored implementation.
The previous worker's pruning is not counted again.

## Where the brief, the DAG or earlier work was wrong

The item is absent from `lean/`, but its rework row identifies a complete archived
module removed after a cluster restore. It is therefore a restoration with zero
holes, rather than a new proof task or an unused module to withdraw. No current
B2 return names additional changes to this item. The source compiles without any
repair to its proof or definitions. No mathematical statement error was found.

The downstream tool reports zero live consumers because these modules are
quarantined. Archive searches find CoefficientHeartGeneration,
RationalClosedSupportConstructible and ProperBaseChangeRational as direct
importers. Their original interface is preserved verbatim, and none is withdrawn
or adapted. No new node is needed and no existing node field changes.

Lean Finder returned general derived-category boundedness infrastructure; Loogle
returned the generic retract API. Source searches found the existing upstream
homologyProperty_isTriangulated instance and no replacement for this precise
finite-constant-model coefficient theorem. The archived proof already uses the
corresponding generic infrastructure and remains the intended unit route.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
