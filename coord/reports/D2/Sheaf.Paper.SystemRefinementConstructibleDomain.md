## What changed

In Sheaf.Paper.SystemRefinementConstructibleDomain, prove
AlgebraicGeometry.ProEtale.SystemRefinement.restrictionDirect_existsUnique and
AlgebraicGeometry.ProEtale.SystemRefinement.restrictionPull_existsUnique.
The signatures, definitions, existing docstrings and public imports are preserved.

The quotient maps form a natural coefficient square with constant direct image.
Adjunction transports this to the inverse-image coefficient square. Specialize
Scheme.proEtaleRingRestrictionDirectImage and its proved identity section formula,
then use its inverse for the item's required orientation. The inverse-image
comparison specializes Scheme.proEtaleRingRestrictionPullbackInv. Its Hom-equivalence
formula is the stated unit normalization, and injectivity proves uniqueness.
Only proved private helpers and two private proof imports are added. The DAG
records these dependencies and the actual argument. No other modules are adapted.
The full item compiled through lcompile.py with both proofs in 51.8 seconds.
The profiler settings and temporary probe were then removed; delivery recompiles
this final source. General private ring-sheaf lemmas keep the finite-coefficient
specialization from repeatedly unfolding large chosen functor implementations.

## Proved and sorry left

Two of the six original holes closed, by declaration name:
AlgebraicGeometry.ProEtale.SystemRefinement.restrictionDirect_existsUnique;
AlgebraicGeometry.ProEtale.SystemRefinement.restrictionPull_existsUnique.
Zero holes added; zero split off.

Four original holes remain, all with node
lem-pur-system-refinement-constructible-domain and their original complete
source/proof docstrings:
AlgebraicGeometry.ProEtale.SystemRefinement.scalarPull_existsUnique;
AlgebraicGeometry.ProEtale.SystemRefinement.gamma_witness_evaluation;
AlgebraicGeometry.ProEtale.SystemRefinement.theta_evaluation;
AlgebraicGeometry.ProEtale.SystemRefinement.normalized_operations.

## No longer needed

No existing import, node or module is removed. The two proved comparisons need
no new K-flat calculation: the ordinary compatible ring-sheaf-change theorem
already gives the required inverse-image comparison. Remaining node proof steps
and dependencies are retained for the four untouched holes. No module is withdrawn.

The ordinary ring-sheaf-change interface is reused as an auxiliary tool from
lem-weil-pbc-ring-sheaf-change-adjunction. No tool_uses approval is added by
the worker; the independent reviewer should record any required approval.

## Where the brief, the DAG or earlier work was wrong

No statement was changed or disputed. The ordinary restriction comparisons have
already been proved in the compatible ring-sheaf-change interface; specialization
requires checking the actual composite quotient maps, the orientation of the
section-normalized direct comparison, and the adjunction unit formula.

The construction works when m = n, for empty schemes, and with nonflat quotient
maps: the naturality equation is for arbitrary tower arrows and no flatness or
common cohomological bound enters either proof.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
