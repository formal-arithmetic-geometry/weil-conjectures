## What changed

Replaced the proof of `AlgebraicGeometry.ProEtale.ChartFiniteRing.chartFiniteRingAdjunction`
by assembly from the existing chart-domain declarations, the ordered affine adjunction,
the fixed compact-support comparison, and full-subcategory adjunction restriction.
The proof retains both counit equations, the intrinsic domain, the canonical geometric
comparison, and the Brown uniqueness assertion. The theorem signature is unchanged.

The normalization components are evaluated from natural isomorphisms; the geometric
component keeps its explicit endpoints. The generic public comparisons keep the
coefficient category explicit and make naturality available without expanding concrete
module tensor constructions.
Private helpers prove the intrinsic predicate conversion, twist flatness, and the
one-ring assembly. The transfer owner exposes its existing categorical construction
as `etaleProEtaleAdjunctionTransferOfComparison`, with its old theorem applying it.
The item uses this construction with the supplied fixed comparison.
`transportUniqueCounitIso` proves the final unique comparison after changing from
the transported right functor to the specified geometric right functor.
The geometric comparison is the fully faithful lift of the ambient natural
isomorphism, composed with the actual equivalence counit.
No source-library file is changed. The existing, unclaimed Sheaf module
`AffineTraceRightNormalForm` exposes eleven proved generic helpers; the duplicated
item helpers are direct abbreviations of them. Their mathematical bodies are unchanged.

Change record: `coord/changes/G4-chart-finite-ring-normalization.md`.
Validation: the main item compiles cleanly against the sandbox overlay (53.2 s,
exit 0). Both shared owners and the unchanged `OrderedAffineTraceNormalForm`
consumer compiled in the same remote batch. The final batch also compiled both
shared owners, the item, and the unchanged `ChartCounitScalarTransport` consumer
together (exit 0 throughout). The theorem signature and entire `Datum` structure are unchanged.
The packet adds no DAG cycles relative to the current shared repository.

## Proved and sorry left

Closed the one original hole,
`AlgebraicGeometry.ProEtale.ChartFiniteRing.chartFiniteRingAdjunction`
(node `lem-sp-chart-finite-ring-adjunction`). No holes are added or split off.
The item contains zero `sorry`. Both adapted helper modules also contain zero
`sorry`; none are added anywhere in the packet. This is one hole closed and zero
holes added, with zero split-off statements.
The imported chart-domain theorems remain separate existing items.

## No longer needed

Removed public imports:

- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`
- `Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses`
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.SecSmoothPurity.ReductionDirectImage`
- `Sheaf.Paper.FiniteLocalizingExceptionalPreservation`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`

The proof uses the comparison equivalences bundled by `etaleCtfChartDomain`, so it does
not separately apply `det-pe-finite-tor-comparison-noetherian`. No coefficient-change
argument is needed: the two rings are treated independently. The graph-normalized
`chartLeftOnPlus` already exists, so `lem-sp-chart-left-scalar-normalization` is not needed
for this adjunction proof. The existing `fixedCompactSupportComparisonIso` is already an
isomorphism on bounded-below inputs, so no additional application of
`lem-sp-finite-compact-support-domains` is needed. Mathlib supplies Noetherian permanence,
adjunction composition, full-subcategory restriction and right-adjoint uniqueness;
there is no separate use of `lem-weil-pbc-finite-type-over-noetherian`,
`def-weil-pbc-composite-adjunction`, `sk-prop-sf-rf-shriek-preservation`, or
`det-sp-unique-right-adjoint`. The generic Brown restriction argument in the transfer
module proves precisely the conditional Brown clause required here.

These are removals from this item's proof dependencies, not withdrawals of modules or
claims that the corresponding nodes are globally unused. Statement dependencies and
the blueprint unit route are preserved.

## Where the brief, the DAG or earlier work was wrong

The planned left scalar-normalization module is absent, but the required left
comparison is already defined in this item. Its scalar compatibility is not required
by this theorem. The transfer theorem's fixed-comparison hypothesis uses a differently
packaged canonical compact-support comparison; the categorical proof is independent of
that extra equality. The public categorical transfer helper retains the supplied fixed
comparison and proves its actual counit equation directly.

The earlier normalization definitions hide naturality behind componentwise expressions.
The refactoring records natural isomorphisms explicitly; its defining maps and downstream
normalization require independent review under the accompanying change record.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
