## What changed

The assigned theorem is proved from the ordinary flat scalar/common-quotient tensor
comparison. A private helper proves preservation of native K-flatness by flat scalar
restriction, using the exact section-action tensor equivalence. The main proof computes
both composites on native K-flat resolutions and descends the ordinary isomorphism
through the universal localization computation counits. The two successive integral
restrictions are combined with the actual pointComparison inverse, so the theorem's
statement and both specified functors are unchanged.

Proof imports add the ordinary comparison module and the existing resolving-square,
internal-section tensor, flat-restriction, and native scalar computation APIs. Existing
large coefficient, module functor and sheaf monoidal definitions are locally irreducible
during elaboration; their definitions are unchanged. No source-library declaration or other group's module is changed.

## Proved and sorry left

Closed: AlgebraicGeometry.ProEtale.internal_first_residue_reduction_comparison
(lem-sfb-internal-first-residue-reduction-comparison), by a complete Lean proof from the
ordinary comparison.

Added: AlgebraicGeometry.ProEtale.internal_first_residue_ordinary_comparison
(lem-sfb-internal-first-residue-ordinary-comparison), the sole remaining sorry.
This is a decomposition: one upper hole closed and one ordinary-module hole added.
The delivery has declaration-hole net zero; target-closure counts are the ledger’s.
The lower statement contains no complexes, derived categories, K-flat resolutions or
localization. It requires only the flat coefficient map and its ordinary common-quotient
tensor comparison. It is not the derived comparison under another name.

The private firstResidueRestrictionKFlat, firstResidueDerivedSquare,
firstResidueRestrictionComp, firstResidueComposeSquare and
firstResidueTwoRestrictionSquare helpers are completely proved.

## No longer needed

No original imports removed. The parent now needs only the ordinary comparison for its
coefficient calculation, rather than the full integral constant-completion equivalence,
fixed normalized integral section squares and internal-section scalar adjunction directly.
The parent does not separately use lem-sf-finite-discrete-normalized-encoding,
det-pe-derived-nakayama-resolution, def-weil-l-adic-coefficient-extension,
lem-sfb-integers-coset-basis, det-prop-integral-criterion-constant-coefficients,
lem-pe-fixed-integral-section-squares, lem-sfb-internal-section-scalar-adjunction or
def-weil-pbc-internal-abelian-sheaf-module-equivalence. The ordinary child retains the
coefficient dependencies it actually needs. No module is withdrawn or claimed globally
unreachable: these dependencies may still be needed by the child or other consumers.

## Where the brief, the DAG or earlier work was wrong

The local shared mirror omitted the assigned item although its node and current live
server source existed. The exact current source was recovered read-only from the server.
There was no quarantine or rework row for it. The mathematical statement is unchanged.

The existing plan's unbounded-derived step can be performed directly on internal
K-flat resolutions, without deriving the section-action and small-site transports anew.
The remaining coefficient calculation belongs to ordinary modules. The empty scheme,
zero module and zero complex impose no additional hypothesis; the ordinary tensor
comparison and localization argument cover them.

## New nodes

lem-sfb-internal-first-residue-ordinary-comparison: the ordinary part of the original
first two proof steps, with the same source, scalar maps and residue ring. Its public
statement records flatness of the actual scalar composite and the ordinary tensor
isomorphism. The parent proves native K-flat preservation and the entire derived
localization step. No definition or existing statement changes, so no change record
is required.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
