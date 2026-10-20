## What changed

Retired the zero-hole duplicate
Sheaf.AlgebraicGeometry.StrictHenselizationSchemeFunctoriality using deleted.txt.
Attached lem-weil-pbc-strict-henselization-scheme-functoriality to the proved
WeilConjectures.AlgebraicGeometry.StrictHenselizationSchemeFunctoriality theorem,
with its exact upstream strictLocalization signature. The existing proof plan
and mathematical dependencies are retained.

Repaired the landing conflict reported for reviewed head 07e72618cb. Current
main contains ca565a83de, which has already withdrawn the Sheaf core-completion
module and attached its node to the upstream core-completion theorem. Removed
the retained packet's stale replacement for that empty module and its stale
parent-node edit. This preserves the landed parent attachment and the existing
CoreData proof instead of restoring the retired declaration.

The upstream completion theorem imports and applies the upstream functoriality
theorem. CoreData already calls that completion theorem and transports its
presentations and structural equalities through the proved private
localizationComparison and localizationComparison_base. Thus no consumer edit
is necessary. No source-library declaration or target is changed.

A server compile of a fresh import/axiom probe passed in 1.2 seconds. The
replacement functoriality theorem, upstream completion theorem and current
CoreData theorem each report exactly propext, Classical.choice and Quot.sound.

Change record:
coord/changes/M2-strict-henselization-scheme-functoriality-retirement.md.

## Proved and sorry left

The assigned retirement item has zero sorry declarations. Holes closed: 0.
Holes added: 0. Split off: 0. No sorry remains in a delivered Lean file.
The replacement exists_strictHenselizationSchemeMap, the upstream
exists_compatibleStrictHenselizationCoreCompletion, and the current
exists_compatibleStrictHenselizationCoreData are proved declarations.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.StrictHenselizationSchemeFunctoriality,
including its duplicate exists_strictHenselizationSchemeMap and its private
fullStrictHenselizationCone and pointedPullback. Its public import of
Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap leaves with it; that
structural-map module is still needed elsewhere and is not withdrawn.

The old packet's smallStrictLocalizationIso, smallStrictLocalizationIso_over
and smallStrictLocalization_fiber_eq_closedPoint adaptations are unnecessary
because ca565a83de has already migrated the parent and its consumer. They are
removed from the packet. No extra Lean module is delivered or withdrawn.

No DAG node is removed. The sole parent node still requires functoriality and
is already realized by the upstream completion theorem, whose proof uses the
replacement. The two limit/structural-map dependencies remain required. The
unit sk-thm-p1 and its realized statement and proof steps are preserved.
An import scan of lean/ and quarantine/ found no imports of the retired module;
the Paper.StrictHenselizationMapExists mention is historical documentation.

## Where the brief, the DAG or earlier work was wrong

The returned packet assumed the Sheaf core-completion module was still the
consumer. Its restoration would undo ca565a83de. The repair instead preserves
the current empty module, current upstream node attachment and CoreData's
existing comparison proof. This is a real retirement with a replacement proof,
not an unchanged re-push or a withdrawal based only on zero importers.

The inherited citation to Stacks 03Q9 is about higher direct images. The relevant
sources are etale-cohomology.tex, definition-etale-local-rings (03PS), its
following functoriality paragraph, lemma-describe-etale-local-ring (04HX), and
algebra.tex, lemma-strictly-henselian-functorial (04GU). Source metadata remains
maintainer-owned and is not overwritten.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
