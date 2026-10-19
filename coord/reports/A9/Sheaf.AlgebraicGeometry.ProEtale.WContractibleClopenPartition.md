## What changed

Proved AlgebraicGeometry.Scheme.proetale_wContractible_clopen_partition in
Sheaf.AlgebraicGeometry.ProEtale.WContractibleClopenPartition without changing its signature.
The proof takes the finite affine refinement directly from QuasiCompactCover, forms its
finite affine coproduct, uses the existing scheme-level split-cover theorem
AlgebraicGeometry.exists_comp_eq_id_of_isWContractibleRing, and pulls the components back
along the section. It proves closedness using the union of the other pieces, constructs
restricted lifts with IsOpenImmersion.lift, discards empty pieces, and reindexes by Fin.
The construction handles an empty target and an arbitrary original indexing universe.
Updated the existing node's proof and proof dependencies to describe this implementation.
All public imports, definitions, theorem signatures, and visibility are unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
AlgebraicGeometry.Scheme.proetale_wContractible_clopen_partition
(node det-pe-wcb-clopen-partition). Added 0 holes; split off 0 statements.
No sorry remains in any delivered Lean file.

## No longer needed

Removed proof imports Sheaf.AlgebraicGeometry.EtaleComparison and
Sheaf.AlgebraicGeometry.WeaklyEtaleStability. Their bundled theorems are unnecessary:
Mathlib already supplies the weakly etale instances needed for the finite refinement
and its coproduct. Accordingly removed direct proof dependencies
 det-pe-morphisms-etale-comparison and sk-lem-pe-weakly-etale-stability, and withdrew
the two corresponding top-level tool_uses approvals from this node.

Also removed direct imports Mathlib.AlgebraicGeometry.Limits,
Mathlib.AlgebraicGeometry.Morphisms.Affine, Mathlib.AlgebraicGeometry.Morphisms.Etale,
and Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra: needed Mathlib APIs are already
available through the reused source module. The explicit open-immersion-to-etale and
flat-surjective-spectrum steps are packaged in instances and the proved split-cover API,
so lem-weil-pbc-open-immersion-etale and
lem-weil-pbc-flat-surjective-spectrum-faithfully-flat are no longer direct dependencies.
The split-cover step itself is retained, using the existing scheme-level theorem rather
than repeating the ring-map conversion around its recorded ring-level declaration
RingHom.exists_retraction_of_wlocal_geometric_criterion. Its module
Sheaf.RingTheory.WContractibleGeometricCriterion is not needed by this proof.
No module is withdrawn; global pruning depends on other consumers.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error. The planned ring-map conversion and separate bundled
comparison/stability theorem imports were unnecessary because the source library already
proves the required affine section theorem, and Mathlib proves the stability instances.
The unit's finite-affine-refinement, split-cover, inverse-image-partition route is preserved.
No new nodes, interface changes, or consumer adaptations are required. The preflight
requests a change record for the added `Limits` namespace opening; this is documented
in coord/changes/A9-WContractibleClopenPartition.md, including the proof-import pruning
and the unchanged public interface. The module compiles against current server sources.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
