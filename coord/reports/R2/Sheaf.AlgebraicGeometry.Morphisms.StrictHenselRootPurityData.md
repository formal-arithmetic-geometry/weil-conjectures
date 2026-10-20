## What changed

Restored the quarantined module
Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData for the assigned
zero-hole compile repair. Replaced its retired structural-flatness import and
call with a proved private helper using the existing filtered-colimit flatness
API. The helper follows the already repaired small-ring proof in
StrictHenselRootNormalizationGenericEtale.

The public theorem signature, public imports, existing definitions, and the
root-divisor and tame-normalization construction remain unchanged. Updated the
item node's proof, proof_deps and proof_origin to record the colimit argument.
No consumer adaptation is required; the only Sheaf consumer is quarantined,
and its signature and dependency remain valid.

Change record:
coord/changes/R2-strict-hensel-root-purity-data-restoration.md.

## Proved and sorry left

This repair starts with 0 local holes and leaves 0: 0 holes closed, 0 added,
0 split off. No sorry remains in any delivered Lean declaration.

The restored theorem is
AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_purity_data
(node lem-sbc-strict-hensel-root-purity-data).
The private purityData_small_strictHenselization_flat is fully proved.
Both print only propext, Classical.choice and Quot.sound, so neither proof has
a transitive sorry dependency. The complete module compiles cleanly through
lcompile.py in 5.2 seconds, with no warnings. Public signatures and public
imports were checked verbatim against the archive, and every line is at most
100 characters.

## No longer needed

Removed the proof import
Sheaf.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat, which is an
already retired empty stub. Replaced this item's direct proof dependency on
lem-sbc-affine-strict-henselization-structural-flat with the existing
lem-weil-pbc-flat-ring-map-iff-ind-flat and lem-weil-pbc-etale-algebra-flat tools
and the small strict-henselization definitions. The upstream flatness theorem
and its node remain available for other users. No library module is withdrawn
or claimed as newly pruned. The regular-quotient and tame-normalization
modules remain needed and imported; all other original imports remain used.

## Where the brief, the DAG or earlier work was wrong

The missing item source was quarantined, not withdrawn, and already contained
no sorry. The actual repair is the retired flatness call. Importing the
upstream replacement would mix two strict-henselization models with incompatible
structural-map lemma imports. A direct private proof for the unchanged small
coordinate-ring colimit fixes this without a public interface repair or a new
split. The original compile error and resulting unsolved main goal disappear.

LeanFinder returned AdjoinRoot and IsAdjoinRootMonic API results, but no shorter
replacement for the construction. Loogle found no match for flatness of a
ring colimit. msearch grep found no exact match; direct rg located the existing
RingHom.Flat.of_isColimit implementation and the repaired small-ring argument.
The adopted source theorem uses the upstream ring model, so it is not a direct
application at this interface. The blueprint unit route remains unchanged.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
