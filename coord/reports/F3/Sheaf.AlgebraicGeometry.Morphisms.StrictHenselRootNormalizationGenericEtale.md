## What changed

Restored Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale
from the exact quarantine path recorded in coord/rework.tsv. Replaced its retired
proof import Sheaf.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat
with WeilConjectures.RingTheory.ProEtale.FaithfullyFlat. Added the fully proved
private helper small_strictHenselization_structural_flat for the small
coordinate-ring colimit used by the unchanged public statement. Updated the
existing node's proof and proof_deps to reflect that filtered-colimit argument.

The public theorem, its docstring, all public imports, the regular-divisor
argument, the generic source-etaleness application and the finite-morphism
shrinking proof are preserved. The small helper constructs the natural family of
flat neighbourhood structure maps and applies RingHom.Flat.of_isColimit; its
compatibility equation follows from Spec faithfulness and the canonical cone.

Change record:
coord/changes/F3-strict-hensel-root-normalization-generic-etale-restoration.md.

## Proved and sorry left

This is a zero-hole compile repair: the quarantine source had 0 local holes;
0 holes closed, 0 added, 0 split off, and 0 remain. The restored declaration is
AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_normalization_generic_etale
(node lem-sbc-strict-hensel-root-normalization-generic-etale).
The new private helper is completely proved.

The complete restored module compiles cleanly through lcompile.py in 4.7 seconds.
#print axioms for both the public theorem and private flatness helper reports
only propext, Classical.choice and Quot.sound. Thus neither proof has any
transitive sorry dependency. The public signature and public-import list were
also checked verbatim against the quarantined source. The only direct caller is
itself quarantined; its application has the same binders and argument order.

## No longer needed

Removed the proof import
Sheaf.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat, which is an
already-retired empty stub. Removed this item's direct proof edge to
lem-sbc-affine-strict-henselization-structural-flat; its small-colimit instance is
proved here from lem-weil-pbc-flat-ring-map-iff-ind-flat and
lem-weil-pbc-etale-algebra-flat, with the existing strict-henselization definitions.
The upstream flatness theorem and its node remain available for their other users.
No library module is withdrawn or claimed as newly pruned. All other imports and
stated mathematical dependencies used by the existing normalization argument stay.

## Where the brief, the DAG or earlier work was wrong

The missing Lean file was quarantined, not unused or withdrawn. The archive has
no sorry to close: the assigned failure is the retired flatness declaration.
The new upstream theorem cannot be substituted just by changing an import:
the upstream and small colimit rings are canonically isomorphic, not
definitionally equal. Moreover, direct import gives a duplicate-name error for
AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_eq. The local colimit
proof avoids mixing those APIs and preserves this item's original statement.

Searches completed: LeanFinder found RingHom.Flat.respectsIso and of_bijective;
Loogle found no exact RingHom.Flat/RingEquiv match; msearch grep found a composition
example. Reading the source and existing change record exposed both the canonical
comparison and the incompatible structural-map imports. The existing
RingHom.Flat.of_isColimit API gives a direct complete proof without another split.
The unit route and every incoming dependency remain intact.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
