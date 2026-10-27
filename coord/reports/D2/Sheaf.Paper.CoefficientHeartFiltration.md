## What changed

Proved `AlgebraicGeometry.ProEtale.coefficientHeart_filtration` in
`Sheaf.Paper.CoefficientHeartFiltration`, preserving its signature and all four existing
object and morphism definitions. The proof uses the actual open adjunction counits,
`CondensedRing.exists_openFiltrationSuccessor`, Mathlib's image-subobject comparison,
and the existing `Subobject.cokernelOfLEMkIso` from `WeilConjectures.ConstructibleSheaf.Devissage`.
The proved private `nestedOpen_quotient` is the objectwise API for the existing
natural successor theorem, including its comparison to the prescribed closure extension.
The proved private `openPrefix_filtration` carries the construction for any commutative
condensed ring; the public theorem specializes it and appends lisseness. Three proved
generic private helpers keep the image-representative transport,
evaluation–cokernel comparison, and passage from natural successors to image quotients
abstract. Evaluation transports the natural successor quotient to the objectwise cokernel.
The concrete comparison eliminates its isomorphism witnesses directly, avoiding expensive
kernel reductions of locally chosen isomorphism data.

The mixed-factorization comparison is proved by support: the closed-then-open extension
vanishes off the stratum and restricts to its original module. The closed unit reconstructs
it from the closure, and the open counit inside the closure reconstructs it from the
stratum. The factorization proof uses the existing earlier support interfaces directly:
`CondensedRing.openRestrictionPushforwardZero`, `CondensedRing.moduleUnitOfAbelian`,
`ProEtale.abelian_closed_support`, `ProEtale.abelian_open_supported_counit`, and
`mem_essImage_openImmersionLowerShriek_of_mem_essImage`. Lisseness uses
`coefficientHeart_commonStratification_lisse` with the identity refinement.

Repair of the return at head `799b43a04`: removed all four private duplicate declarations
`closedPullback_zero_of_disjoint`, `closedOpenExtension_zero_of_disjoint`,
`moduleClosedSupportedUnit`, and `moduleOpenSupportedCounit`. They are not renamed or
reintroduced. The existing earlier support interfaces listed above now supply the needed
support and adjunction properties within the mixed-factorization argument. The generic
module-unit transport and abelian supported-counit results are imported and used rather
than reproved. Importing `Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection`
itself is impossible: `tools/import_direction.py may` confirms it already reaches this
filtration, so that import would close a cycle. No change to that downstream module is
needed.

Validation: the revised complete module compiled cleanly through `lcompile.py` in 11.2 seconds.
The existing public theorem signature and all four definition bodies were compared verbatim
with the current shared source and are unchanged.

The proof-context change record is
`coord/changes/coefficient-heart-filtration-proof-context.md`. The smallness proof is
registered only as a local instance after all existing definitions; transparency attributes
are also local. The public definitions and statements are unchanged.

All added imports are private proof imports. No source-library file, existing public
signature, public import, definition body, or target statement is changed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.coefficientHeart_filtration`
(node `det-lem-coefficient-heart-filtration`). Added zero holes and split off zero holes.
There are zero `sorry` occurrences in the delivered Lean module. All private helpers are
proved. Existing imported statements remain the responsibility of their own nodes.

## No longer needed

Removed the redundant private import `Mathlib.AlgebraicGeometry.Noetherian` (already
publicly available through common stratification). Removed the direct proof import
`Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence`.
The unit-route imports `Sheaf.Paper.CartesianCoefficients` and
`Sheaf.Paper.CoefficientHeartClosure` are retained, as preflight requires.
The filtration proof does not need
`lem-sfb-locally-closed-extension-coherence` as a direct proof dependency: support gives the
factorization comparison for the actual normalized condensed-coefficient functors,
and the existing lisse-refinement theorem gives the last clause. The unit's closure
statement and its own proof steps remain in place elsewhere.

The direct import `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf` is replaced
by the support-reconstruction proof import; the former remains transitively imported
and is not claimed as a globally pruned module. No upstream declaration is removed.
Removed the obsolete top-level tool approval for
`lem-sfb-locally-closed-extension-coherence`,
keeping the remaining approvals in their original order.
Global unreachability of the removed direct dependency is not claimed.

The four copied support wrappers named above are removed. Only their existing primitive
interfaces are needed. No library module is withdrawn or claimed globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The returned packet duplicated four private helper statements already present in the
generator-tensor module. This repair removes those declarations and uses the earlier
support and adjunction interfaces directly, avoiding the circular import.

No statement error was found. The planned arbitrary-ring factorization comparison is
unnecessary for this coefficient-specific result; its two required support conditions
can be proved directly with the existing abelian base-change and support lemmas.
The existing common-stratification lisse theorem also avoids using the whole closure
theorem for the final clause. Empty schemes, empty strata, zero modules, equal consecutive
prefixes, and the zero-length stratification require no extra hypotheses or cases.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
