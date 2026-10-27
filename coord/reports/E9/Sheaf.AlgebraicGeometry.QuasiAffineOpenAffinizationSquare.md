## What changed

Proved `AlgebraicGeometry.Scheme.isPullback_toSpecΓ_of_isOpenImmersion` in
`Sheaf.AlgebraicGeometry.QuasiAffineOpenAffinizationSquare`, with its signature unchanged.
The proof imports the two existing declared chart dependencies:
`Sheaf.AlgebraicGeometry.QuasiAffineOpenPrincipalComparisonCover` and
`Sheaf.AlgebraicGeometry.AffinePrincipalAffinizationIsomorphism`.
It proves the inverse-image/range equality pointwise using the principal cover and
surjectivity of each restricted affinization isomorphism. Mathlib's
`IsOpenImmersion.isPullback`, followed by `IsPullback.flip`, supplies the requested square.
The node proof now describes these exact Lean steps; its proof dependencies are unchanged.
Both imports passed the import-direction check, and the module compiled through lcompile.py.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.isPullback_toSpecΓ_of_isOpenImmersion`
(node `lem-a1-quasi-affine-open-affinization-square`).
Zero holes remain in the item; zero holes were added or split off.
The proof uses the existing declarations
`AlgebraicGeometry.Scheme.quasiAffine_open_principal_comparison_cover` and
`AlgebraicGeometry.affine_principal_affinization_isomorphism`, which still have their
pre-existing sorry proofs in the shared library. They are the already stated dependencies,
not new statements or new holes in this delivery.

## No longer needed

Removed the direct proof import
`WeilConjectures.AlgebraicGeometry.InvertibleSectionLocalization` and the stale node
`tool_uses` approval `lem-sc-p1-invertible-section-localization`.
The localization module remains a transitive dependency of the existing affine-principal
lemma, so no module or node is claimed as globally pruned. All declared proof dependencies
remain needed, and no unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. The existing source import and `tool_uses`
entry named the underlying localization theorem rather than the two chart results extracted
in the later DAG re-split. The Lean proof now follows those existing statements.
Mathlib's affine-morphism affinization square is not used: a general open immersion need
not be affine, and that square has a different bottom-left vertex.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
