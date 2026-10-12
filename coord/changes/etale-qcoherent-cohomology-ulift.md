# AlgebraicGeometry.Scheme.Modules.nonempty_etaleTensorSectionsSheaf_cohomology_ulift

## Reason

The additive-vanishing target needs a comparison between coefficient universes.
Existing curve vanishing is stated for small coefficients, while its derived target
uses lifted coefficients. The existing affine lifted acyclicity does not itself
state a comparison of their global cohomology. This addition isolates that step.

## Old

No declaration existed. Every existing signature and definition is unchanged.

## New

```lean
theorem nonempty_etaleTensorSectionsSheaf_cohomology_ulift (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated] (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) : Nonempty (Sheaf.H ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (etaleTensorSectionsSheaf F)) q ≃+ Sheaf.H (etaleTensorSectionsSheaf F) q)
```

The new theorem is stated in `Sheaf.AlgebraicGeometry.EtaleQcoherentCohomologyULift`.
It compares cohomology groups and asserts no vanishing or dimension bound.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierAdditiveVanishing | H1 | Uses the new comparison in its proof; original signature retained. |
| Sheaf.AlgebraicGeometry.EtaleQcoherentCohomologyULift | H1 | New module, one named open theorem; no previous users. |

There are no prior downstream users of the added declaration. No existing public
imports change, and no target meaning changes.

## Status

landed 20261012T070537-L-3471264 2026-10-12 (merge of deliver/H1/Sheaf.AlgebraicGeometry.Curve.ArtinSchreierAdditiveVanishing)
