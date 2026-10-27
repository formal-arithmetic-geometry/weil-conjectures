## What changed

Proved `AlgebraicGeometry.ProEtale.SupportedScalarTorInterval.supported_scalar_tor_interval`
without changing any signature or definition. The proof constructs the two invertibility
instances, tests the Tor hypothesis on the degree-zero coefficient module using a K-flat
resolution, carries vanishing through exact open extension, and reflects it through the
faithful exact intrinsic comparison on module sheaves.

The tensor test uses the existing normalized `scalarMateDerivedTensorIso`, the scalar
extension K-flat computation, exact restriction factors, and `scalarMateOrdinaryComplexIso`.
No tensor presentation, arbitrary comparison map, or auxiliary statement is introduced.
All original public imports stay unchanged. Added private proof imports for the existing
K-flat resolution and exact-derived-functor cohomology APIs. Updated the item's DAG proof
and dependency union to match this argument. The unit's extension-by-zero route is retained.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.SupportedScalarTorInterval.supported_scalar_tor_interval`
(node `lem-sp-supported-scalar-tor-interval`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
The proof uses existing named dependency theorems, some still unproved in their own modules.
The module compiled cleanly through lcompile.py; delivery also runs the axiom probe.

## No longer needed

Removed private imports:
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`;
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`;
- `Sheaf.Paper.ComparisonPullbackExact`.

The proof does not use the fixed-coefficient theorem `proEtale_extension_by_zero`
(`lem-cbc-proetale-extension-zero`): the actual intrinsic open extension already has exactness,
and its canonical scalar-restriction isomorphism is `openRestriction` in the already imported
`IntegralCompactSupportCoefficientData` module. It does not use
`finiteCoefficientInverseImageMap_isIso` (`prop-weil-pbc-proetale-constant-ring-map`): the
existing normalized coefficient pullback supplies the required identification directly.
It does not use `comparisonPullbackExact` (`lem-sf-comparison-pullback-exact`): generic exact
functor cohomology commutation applies directly to the intrinsic comparison, and module
faithfulness comes from `proEtaleClassicalSheavesModules`.
These three nodes were removed from proof_deps and their obsolete tool_uses entries removed.
The constant-ring node remains a statement dependency; no claim of global unreachability or
withdrawal is made. No module or declaration is deleted. No source-library import changes.

## Where the brief, the DAG or earlier work was wrong

The plan is mathematically sound. Its first step needs an explicit bridge between the
resolution-based Tor predicate and the arbitrary supplied tensor model. The normalized
scalar comparison, K-flat scalar-extension computation, and ordinary complex comparison
provide that bridge without a new lemma. The existing `exists_isKFlatResolutionGeneral` theorem supplies precisely the
live K-flat predicate used by the original Tor-amplitude definition.

The exact derived-functor API already proves both preservation and faithful reflection of
zero cohomology, so the specialized comparison cohomology theorem is unnecessary here.
Faithfulness is used only on module sheaves, never on the unbounded derived category.
No boundedness, constructibility, flatness of B/A, finite projective dimension, nonempty-open,
or nonzero-coefficient assumption is added. The proof covers the empty open and zero rings.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
