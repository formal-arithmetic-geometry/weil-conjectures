## What changed

Repaired and proved `WeilConjectures.normalizedDVR_roos_augmentation` in
`Sheaf.Paper.NormalizedDVRRoosAugmentation`. The selected level comparison now
retains its finite coefficient action: a finite-coefficient complex `N`, a chain
isomorphism `iN`, a finite-derived isomorphism `eN`, and their comparison equation
`hN`. Completed-derived successor compatibility alone was insufficient.

Added two fully proved auxiliary modules:
`Sheaf.Algebra.Homology.RegularQuotientConeAdjoint` proves the strict quotient-cone
adjoint formula, first on K-flat complexes and then by resolution and naturality;
`Sheaf.Paper.NormalizedDVRStrictCoefficientAdjoint` specializes the formula to the
actual completed DVR projection and transports it to the specified adjunction.
These are genuine finite coefficient steps, with no tower or homotopy limit in
their statements. The item then follows by cone coordinates and adjunction
naturality along the canonical homotopy-limit projection. The calculation uses
the zeroth tail term directly; cone naturality composes its reduction with the
projection to obtain the original level projection, without transporting indices.

Adapted the unclaimed `Sheaf.Paper.NormalizedDVRBoundedFreeCone` to accept and pass
the same finite coefficient data. Adapted the unclaimed
`Sheaf.Paper.NormalizedDVRAdicConeModel` to supply them using its existing
`finiteModel n`, identity chain isomorphism and `finiteModel.iso`.
Its statement and all target statements remain identical. No definition changes.
Existing public imports remain verbatim; the added imports are proof imports.
Updated the three existing nodes and added two nodes matching the new lemmas.

Validation: all five Lean modules compile without errors or warnings through
`lcompile.py --all`. The item compiles in about 23 seconds; both consumer modules
also compile. The final adic-model signature was compared verbatim with the source.

## Proved and sorry left

The item initially had one hole, in
`WeilConjectures.normalizedDVR_roos_augmentation`. Its corrected statement now
has a complete proof. The original arbitrary-comparison statement is false; this
is a statement repair with proof, not a proof of that false statement.

Also fully proved
`SheafOfModules.RegularQuotientCone.augmentation_adjoint` and
`WeilConjectures.normalizedDVR_strict_coefficient_adjoint`.
No `sorry` remains in the item or either new module. No hole was added, and no
unproved statement was split off. The two adapted consumer modules contain no
new holes. The existing imported normalized quotient-cone results are used as
stated; no definition is filled by choosing arbitrary unproved existence data.

## No longer needed

No existing import was removed and no module was withdrawn.
The direct proof no longer needs the original node's separate regularity,
projection-divisibility, principal-Koszul and regular-quotient-augmentation edges:
the removed direct edges are `lem-pod-completed-integral-scalar-regular`,
`lem-sp-completed-integral-projection-divisibility`,
`lem-a1-principal-koszul-strict-replacement`, and
`lem-cbc-regular-quotient-cone-augmentation`. These calculations are retained
transitively inside the proved finite coefficient adjoint helper and its regular
quotient augmentation. They are not globally
pruned. The strict normalized adic cone-limit theorem is needed here only for its
normalization API and cokernel descent, not for its limit comparison.
Successor compatibility `heU` does not enter this individual projection calculation;
it is retained in the existing interface and is used by the bounded-free transport.
There is no appeal to preservation of homotopy limits by scalar reduction, nor to
fullness of derived restriction. No module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (original statement): completed-derived level isomorphisms
respecting successors can carry Bockstein twists that do not arise from the finite
coefficient category. Let R be a coefficient DVR and B_j=R/(pi^j), with tower
B_j direct-sum B_j[1]. Modify only the first level comparison by the unipotent
matrix with off-diagonal Bockstein B_1 -> B_1[1]. Precomposition with B_2 -> B_1
kills the Bockstein, so every successor equation persists. The homotopy limit is
R direct-sum R[1] and its projection kills the twist. The scalar-cone augmentation
sees the nonzero twist. Naturality with both summand idempotents forces a natural
coefficient comparison at this limit to be diagonal, so it cannot absorb it.
Thus the old second proof step does not follow from successor compatibility.

The repaired finite coefficient data exclude precisely this problem and are
already present in the canonical strict model. They handle n=0, zero towers and
empty schemes. Both direct DAG citers are adapted in this delivery, and the full
Lean downstream list is audited in the change record. The final adic-cone-model
statement is unchanged; the unit's realized route is preserved.

## New nodes

`lem-cbc-regular-quotient-cone-adjoint` matches the fully proved generic strict
quotient-cone adjoint formula. Its proof uses the normalized ordinary adjunction,
the existing regular quotient augmentation and K-flat resolution naturality.

`lem-coef-normalized-dvr-strict-coefficient-adjoint` matches the fully proved
finite coefficient specialization and comparison transport by localization and
uniqueness of adjoints. It has no tower or limit hypothesis.

Change record: `coord/changes/W3-DVR-strict-coefficient-augmentation.md`.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
