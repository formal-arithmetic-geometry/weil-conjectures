## What changed

Completed the listed retirement of Sheaf.AlgebraicGeometry.ConormalWedgeLocalSpan
in favour of WeilConjectures.AlgebraicGeometry.ConormalWedgeLocalSpan.
The original item already compiled and contained zero sorries.

Its sole direct consumer, Sheaf.AlgebraicGeometry.SelfTorLocalWedgeCoordinates,
now privately imports the upstream theorem and the existing
Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPresheafComparison API.
The new private exterior_span_transport helper pairs each exterior presheaf with
its pure-wedge maps. The presheaves are equal and the wedge maps agree by
reflexivity, so the dependent pairs are equal. Transporting the entire
restriction-and-span predicate along this equality gives the original conclusion.
The private conormal_wedge_mem_span_locally_compat helper applies that result to
the upstream local-span theorem. The generator type is supplied explicitly to
avoid expensive inference through tensorPullback. Scoped local irreducibility
keeps tensorPullback, tensorPullbackObj, sheafification and exteriorSheafRestriction
abstract while elaborating the two new helpers; the scope ends before all existing
helpers. One existing private helper
calls this compatibility result. All existing signatures, visibility, definitions,
docstrings and public imports of the consumer are unchanged. No upstream file
is edited.

The local-span node now attaches to the upstream declaration, with its exact
upstream signature. The parent node records the comparison transport and its
existing comparison dependency. The change record is
coord/changes/q7-retire-conormal-wedge-local-span.md.

Validation: the original module compiled (10.6 s); the final adapted direct
consumer compiled without warnings (22.0 s). The full delivery axiom probe
completed in 20.7 s with SHEAF-PROBED 1 and no axiom or direct-sorry findings.
The consumer's public signature compares byte-for-byte equal to the original. Its full source import closure
has 1429 modules, no Sheaf/upstream twin pairs and no reference to the withdrawn module.
The delivery checks additionally inspect axioms and the complete packet.

## Proved and sorry left

Original item: 0 holes. Closed: 0; added: 0; split off: 0.
No sorry remains in any delivered Lean file.
The new private AlgebraicGeometry.exterior_span_transport and
AlgebraicGeometry.conormal_wedge_mem_span_locally_compat theorems are fully proved
from the existing upstream theorem and proved comparison API.
AlgebraicGeometry.exists_local_wedge_selfTor_coordinates remains proved with its
original signature. No existing proof is replaced by a hole.

## No longer needed

Retired lean/Sheaf/AlgebraicGeometry/ConormalWedgeLocalSpan.lean through deleted.txt.
Removed its sole consumer's private import of
Sheaf.AlgebraicGeometry.ConormalWedgeLocalSpan, replacing it with the upstream
module and the existing comparison module. Its local copies of
exterior_section_map and exterior_section_smul disappear with the module.

No mathematical node or proof dependency is pruned. Node
new-e3-conormal-wedge-local-span remains needed by
new-h3-self-tor-local-wedge-coordinates and is preserved with its upstream Lean
attachment. Its conormal-section and localization dependencies remain used by
the upstream proof. All unit statements, steps and routes are retained.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed item, but this assignment is a listed
retirement repair with zero holes. A no-op compile would not perform that repair.
The apparent API mismatch is the two exterior-sheaf implementations, already
bridged by the library's proved presheaf equality. The private map/smul helpers
named in the retirement row are not exported API. Pairing the equal presheaves
with their identical pure-wedge maps preserves wedges in every degree, including
degree zero, and needs no nonzero-ring, regularity or finiteness assumptions. Empty W has no point satisfying hx.
No false mathematical statement or unit-route defect was found.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
