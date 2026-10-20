## What changed

Simplified the private purityData_small_strictHenselization_flat proof in
Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData. Apply
strictHenselization_indEtale_of_affine_chart to the identity chart, using hb
to identify the algebra structure. Forget its filtered etale-algebra
presentation to modules and apply ModuleCat.flat_of_colimitPresentation.
This replaces the duplicated pointed-neighbourhood cocone and its compatibility
proof. Added only the private import of
Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale.

The root quotient, Cartier divisor and finite normalization argument is
unchanged. Every public signature, public import and definition body is
unchanged. Updated the item's existing node proof, proof_deps and proof_origin
for the actual route. No new nodes or consumer adaptations are needed.
Change record: coord/changes/E1-strict-hensel-root-purity-ind-etale.md.

## Proved and sorry left

The current item starts with 0 sorries and ends with 0: 0 holes closed,
0 added, 0 split off. No sorry remains in any delivered declaration.
The public theorem is
AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_purity_data
(node lem-sbc-strict-hensel-root-purity-data).
Its private flatness helper and the public theorem each print exactly
propext, Classical.choice and Quot.sound. Thus the new route adds no
transitive sorry dependency either. The revised module compiled cleanly via
lcompile.py in 3.8 seconds, with no warnings.

## No longer needed

No import is removed and no module is withdrawn. The source-library flatness
module remains needed for its module-colimit theorem. The item's proof no
longer directly uses RingHom.Flat.of_isColimit or the node
lem-weil-pbc-flat-ring-map-iff-ind-flat; it uses the existing
lem-weil-pbc-flat-colimit-presentation-same-universe and
lem-weil-pbc-strict-henselization-affine-chart-ind-etale instead. This is a
local dependency change, not a claim that those other declarations are unused
throughout the library. No library module is newly pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned rework row describes an error already fixed by the landed R2
restoration. The current source exists, contains no sorry and compiles before
this delivery. This packet makes a substantive shorter proof, rather than
claiming to close a nonexistent hole or repeating the restoration. It preserves
the quarantine archive, attachment and parent dependency.

LeanFinder returned eight AdjoinRoot/IsAdjoinRootMonic API results, but no
replacement for the complete geometric construction. Loogle reported unknown
identifier Ideal.Quotient for the query AdjoinRoot, Ideal.Quotient; this is not
evidence of nonexistence. The msearch grep returned no hits for the chart and
colimit lemma names. Direct rg in the library located the already proved
affine-chart theorem, the colimit-flatness theorem and their application in
StrictHenselRootNormalizationGenericEtale. Their signatures fit the identity
chart without changing the statement. Import-direction checking permits the
new import.

The identity-chart specialization works also for n=1 and needs no regularity
hypothesis. The geometric point supplies chart membership, so it does not
assert a filtered empty colimit. The existing divisor argument still assumes
g is a nonunit and uses positivity of the group order. The blueprint unit's
root-extension and tame-normalization route is preserved.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
