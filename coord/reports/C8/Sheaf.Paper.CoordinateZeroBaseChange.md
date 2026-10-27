## What changed

Filled both theorem proofs in `Sheaf.Paper.CoordinateZeroBaseChange` without
changing any declaration signature, definition, attribute, or import.
The final remote single-file compile passed cleanly in 22.5 seconds with no
errors or warnings.

`pulledExceptional_origin` first uses the existing bounded-below exceptional
inverse-image theorem on the Noetherian affine tower. It extracts its bounded
etale representative, applies exact etale inverse image, and transports that
representative through the derived comparison/pullback isomorphism and the
identification of derived inverse image with the exact induced functor.

`pulledTarget_plus` transports `target_plus` on the new tower through the
existing `targetPullbackIso`. Both arguments implement the existing docstrings;
there is no new proof route or node, and no exceptional-base-change
invertibility assertion is used.

## Proved and sorry left

Closed 2 of 2 holes:

- `AlgebraicGeometry.ProEtale.AffineZeroPurity.pulledExceptional_origin`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.pulledTarget_plus`

Both belong to `def-pur-coordinate-zero-base-change`. No sorry remains in the
item, and no hole was added or split off. The proofs use existing library
declarations, including the still-open `target_plus`; they do not claim to
close the transitive dependencies of those declarations.

## No longer needed

None. Both public imports remain necessary for the existing signatures and
definitions. No new import was added. No node, module, or unit step is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No defect was found in these statements. The node has no numbered proof steps;
the existing theorem docstrings provide the two arguments implemented here.
The general exact-pullback and site-comparison API already suffices, without
new intermediate statements. The arguments include rank zero, identity or
arbitrary base change, and empty schemes without additional hypotheses.

Searches used the prescribed msearch LeanFinder, Loogle, and grep interfaces
and local ripgrep. LeanFinder returned generic derived-category bounds; Loogle
and msearch grep gave no exact hit. Local search found the existing
`comparisonUpperStarCompUpperStarIso`, `isGE_mapDerivedCategory_obj`,
`plusEtaleOrigin_rightDerivedUpperShriek_obj`, `targetPullbackIso`, and
`target_plus` used in the proofs.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
