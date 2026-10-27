## What changed

Kept the statement of `properScalar_transport` verbatim. Its proof separates
intrinsic realization from change of site, applies the existing proved
`ProEtale.etaleProEtale_scalar_mate`, and uses naturality to insert the arbitrary
isomorphism `eHB`. The scalar-extension lower bound comes from `HB.property`
transported through `eHB`.

Added `properSiteIso_hom_ambient` in
`Sheaf.Paper.FiniteProperSiteAmbientNormalization`, proved
from the existing private `ProEtale.sp_comparison_hom` via `import all`. It
identifies the specified included D+ comparison in `properSiteIso` with the
specified ambient counit mate. No comparison is replaced by an arbitrary one.

Added `realizationScalar_directImage_mate` in
`Sheaf.Paper.FiniteRealizationScalarMate` for the
unbounded realization part of the original argument. This statement has no
change of site, properness, boundedness, chosen etale origin, or isomorphism
`eHB`. The proof of the item combines this part with the existing fixed-site
mate theorem and the proved included-site normalization. No existing definition,
public import, or declaration signature changes.

Validation: all three modules compiled through `lcompile.py`; the final item
compile took 30.4 seconds and emitted no warnings. Its statement is byte-for-byte
identical to the repository statement. New node signatures were checked against
their Lean declarations, and all recorded dependencies exist.

## Proved and sorry left

Closed the item's one syntactic hole in
`AlgebraicGeometry.Scheme.FiniteCompactScalar.properScalar_transport`.
Proved the new
`AlgebraicGeometry.Scheme.FiniteCompactScalar.properSiteIso_hom_ambient`
without adding a hole to its proof.

One hole is added and remains:
`AlgebraicGeometry.Scheme.FiniteCompactScalar.realizationScalar_directImage_mate`
(node `lem-finite-realization-scalar-mate`). It isolates the realization and
restriction cube, followed by scalar transposition, on the entire unbounded
fixed-scalar pro-etale category. Its docstring and node give the complete
argument in words. The item module has zero holes. This is a decomposition:
one hole closed and one added among delivered declarations. No net proof
progress is claimed; the ledger measures the entire targets' import closure
separately.

## No longer needed

Removed the item's unused private import of
`Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`; the main
proof uses the proved fixed-site scalar mate instead. The restriction
comparison remains a planned dependency of the smaller realization lemma.

No module is withdrawn. The original plan's K-injective realization calculation
is delegated to the strictly smaller realization-only node; its dependencies
remain needed there. The fixed-site scalar comparison and bounded-to-unbounded
normalization are used through their existing proved declarations. The
original `lem-pur-etale-scalar-mate-projection` is not a separate step of this
proof: the proved fixed-site scalar-mate theorem already identifies that
etale scalar mate. Its module remains needed transitively, so no global pruning
is claimed. The whole SP projection theorem node is not a dependency of the new
normalization: only its already proved private included-site calculation is
used, with the canonical D+ mate node recording the mathematical input.
No blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The D+ versus ambient comparison step already has a complete proof in
`SpDirectImageEtaleMate` (`sp_comparison_hom`, private). Importing that proof
avoids reopening its included-adjunction calculation. Likewise the complete
fixed-site scalar-mate proof is reused. The first preflight found a DAG cycle
caused by citing the entire
`lem-sp-direct-image-etale-mate-isomorphism` node for its private included-site
helper. That node also covers later exceptional/projection arguments and
therefore reaches this item through unrelated dependencies. The normalization
node now records the private helper's actual mathematical input,
`lem-weil-pbc-comparison-direct-image-canonical-mate`, together with the ambient
comparison definitions. The later projection theorem is not used. The Lean
proof remains the same reuse of `sp_comparison_hom`.

Removed an unnecessary `open scoped CategoryTheory.Functor` from the item to
preserve its existing command interface. Added the separately required
Leansearch search record to both new nodes. No false statement, weakened
statement, or definition repair was found. The arbitrary `eHB` is handled by
naturality,
not by selecting a special representative of scalar extension.

## New nodes

`lem-finite-proper-site-ambient-normalization` records the proved included-site
normalization and its exact Lean statement. It lies in the same chapter and
unit as the item and uses the existing normalized comparison proof.

`lem-finite-realization-scalar-mate` records the remaining unbounded
realization/restriction calculation and scalar transposition. It is a proper
part of the argument: it knows nothing of etale origin, bounded comparison,
properness, or `eHB`. The item requires an additional fixed-site mate theorem
and a nontrivial naturality calculation to combine it with site comparison.
No change record is needed because no existing statement or definition changes.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
