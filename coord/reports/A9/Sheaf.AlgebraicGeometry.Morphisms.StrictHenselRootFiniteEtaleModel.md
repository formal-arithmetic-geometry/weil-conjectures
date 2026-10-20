## What changed

Simplified the proved private finiteEtaleModel_small_strictHenselization_flat
helper in Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel.
Apply strictHenselization_indEtale_of_affine_chart to the identity chart with
the algebra structure induced by b and compatibility hb. Map its filtered
etale algebra presentation to modules, use etale-stage flatness, and apply
ModuleCat.flat_of_colimitPresentation. This replaces the repeated construction
of the small coordinate-ring cocone and its conversion to the structural map.

Added the private proof import
Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale. Existing public
imports, public signatures and the finite-etale extension proof are unchanged.
The module compiles in 5.9 seconds. A scratch compilation prints exactly
propext, Classical.choice and Quot.sound for both the private helper and the
public theorem. A separate importing consumer probe compiles with the original
quarantined signature verbatim and the existing argument order.

Updated lem-sbc-strict-hensel-root-finite-etale-model's proof, proof_deps and
proof_origin to describe this shorter route. The node's statement and Lean
attachment, the incoming parent dependency, and the unit's trait/root/purity
route are preserved. Change record:
coord/changes/A9-strict-hensel-root-finite-etale-ind-etale.md.

## Proved and sorry left

This assigned rework item has zero holes in the current source and in the
quarantined original. Holes closed: none (0 of 0). Holes added: none.
Holes split off: none. Sorries left: none.

AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_finite_etale_model
(node lem-sbc-strict-hensel-root-finite-etale-model) remains completely proved.
The private finiteEtaleModel_small_strictHenselization_flat is proved by the
shorter argument above. The axioms check includes all transitive dependencies
of the public theorem and reports no sorryAx.

## No longer needed

No import is removed and no Lean module is withdrawn. All direct proof imports
are used. The proof no longer directly constructs the natural transformation
of pointed-neighbourhood coordinate rings, applies RingHom.Flat.of_isColimit,
or converts the representative cone legs to selected colimit coprojections.

The direct proof dependencies def-weil-pbc-strict-henselization-limit,
def-weil-pbc-strict-henselization-structural-map and
lem-weil-pbc-flat-ring-map-iff-ind-flat are replaced by the existing
lem-weil-pbc-strict-henselization-affine-chart-ind-etale and
lem-weil-pbc-flat-colimit-presentation-same-universe. The definitions remain
statement dependencies and the underlying colimit tools remain transitively
needed, so no module is claimed pruned from the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The rework row still records the unknown retired
strictHenselization_structural_ringHom_flat identifier from the quarantined
archive. E2's restoration is already in the current source, which compiles and
has zero holes. This delivery therefore makes a real shorter proof change to
that source; it does not claim to close a hole or to repeat the restoration.
The main theorem and private helper were compared with the current source,
and the public signature was also compared with the archive. No definition
or statement changes and none is disputed.

The prior direct helper's exact conversion is fragile under simplification:
replacing its last exact with simpa only [Category.assoc] exposes a mismatch
between the cone leg and the selected colimit coprojection. The new proof
uses the stable chart interface already proved in the library. Searches with
msearch.py (leanfinder, loogle, grep) and rg found this route; no new theorem
or node is introduced. All supporting declarations used here are proved.

The identity chart contains the geometric point without a divisor hypothesis.
The unit and nonunit branches and the positive group-cardinality argument
remain intact. The quarantined parent remains preserved and its theorem call
is exercised in the importing probe. No source-library module is edited.
No other agent or second reader was started, as required by the dispatcher.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
