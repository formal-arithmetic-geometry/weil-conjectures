## What changed

Restored Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility from the quarantine
archive identified by coord/rework.tsv. Replaced the retired LocallyClosedStratification
by the current upstream Stratification in the two theorem conclusions and the private
geometric equivalence. Both conclusions retain their explicit constructibility conjunct.

The etale affine-local predicate now uses FiniteLocallyClosedStratification. Added two
private explicit conversions between that structure with constructibility proofs and
upstream Stratification, retaining the same indices, subsets, scheme domains and
immersion maps. The etale proof converts the local witnesses in each direction. The
pro-etale proof uses the already restored current predicate directly. All existing site
composition, finite-local-system pullback and geometric gluing proofs are retained.

Updated the item's node Lean record and the two geometric proof steps to describe the
current interfaces. Change record:
coord/changes/A3-noetherian-global-stratification-restoration.md.
No source-library module or target signature is changed; no consumer is adapted.

Both equivalences compile cleanly through lcompile.py (repair check 2026-10-21: 5.7 seconds,
exit code 0, no diagnostics).
Because the published build initially lacked a freshly landed dependency object, the
unchanged current sources of FiniteLocallyClosedStratification,
CoefficientConstructibleEtaleModules and CoefficientAffineConstructibleProEtaleModules
were compiled in dependency order as sandbox references. These byte-identical dependency
sources are not part of this delivery. The delivery tool performs the axiom probe.

Repair of the return on head 98ce9c17e2: the independent reader passed the mathematical
repair, but landing failed while opening the absent quarantined module
Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation. This module is neither
imported by this item nor included in its packet. The retained Lean source, node changes
and substantive stratification restoration are preserved; the delivery tool rebuilds
the commit on current origin/sheaf-dag and reruns compilation and preflight. No unrelated
quarantined module is withdrawn or replaced to address that landing failure.

Edge cases: empty schemes and zero-stratum partitions remain allowed, all construction
fields are copied without imposing extra hypotheses, infinite coefficient sets and module
values (for example Z over Z) remain allowed, and no scheme separatedness or reducedness
hypothesis is introduced. Actual scheme factorization maps, rather than image containment,
are still used to pull back local models.

## Proved and sorry left

The preserved archive already had zero sorry. This is a substantive API/restoration repair,
not a new closure of either of its historical holes.

Both existing public theorems remain completely proved:
- AlgebraicGeometry.Scheme.etale_noetherian_global_constructibility.
- AlgebraicGeometry.Scheme.proEtale_noetherian_global_constructibility.

Holes closed in this delivery: zero. Holes added: zero. Holes left in the delivered
module: zero. No statement is split off. The two private conversions are explicit total
structure constructions; no axiom or postponed data is introduced.

## No longer needed

Removed two redundant direct proof imports from the archive:
- Mathlib.CategoryTheory.Limits.MorphismProperty.
- Mathlib.CategoryTheory.Adjunction.Limits.

Their declarations are already available through the retained imports. No mathematical
proof dependency, node, module or unit step is pruned in this restoration. In particular
the gluing-core, pullback-stratification and finite-local-system-pullback dependencies
remain in the proof, and all quarantined parent modules remain needed.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a module with sorry, but this assigned rework item has zero
holes: it is absent from lean/ after a cluster restore was reverted and its archived
proofs refer to the retired LocallyClosedStratification. The two affine-local coefficient
predicates were restored with different current interfaces: the etale predicate uses the
DAG's FiniteLocallyClosedStratification, while the pro-etale predicate uses upstream
Stratification. Treating them as definitionally identical would fail. The explicit
constructibility conjunct makes the interfaces mathematically equivalent, and the
private conversions implement exactly that equivalence without changing the source
mathematics. No mathematical statement or unit route is disputed.

Required shorter-route searches were run with msearch.py: LeanFinder returned eight
Noetherian-scheme/affine-cover facts, Loogle on "Stratification" returned zero hits, and
grep on LocallyConstant.*sheafPullback|sheafPullback.*LocallyConstant returned zero hits.
Local source searches located the existing gluing core, stratification pullback and
proved coefficient_finite_local_systems_pullback used by the preserved argument.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
