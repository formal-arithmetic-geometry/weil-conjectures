# AlgebraicGeometry.schemeTensorShift_first_normalization_core

## Reason

The scheme-specific categorical rewrites repeatedly reconstruct the large total-tensor
and derived tensor instance terms. Proved private generic calculations and local caches
of the existing instances avoid this work. No existing signature or visibility changes. The new binary-square module also uses
two fully proved generic private helpers; its scheme specialization uses the
existing inferred instances directly. The second reader added local caches of
`CochainComplex.HasMapBifunctor` in both modules after reproducing a 60-second
timeout. These cache only the existing total-tensor existence proofs. The binary
module also reuses the normalization module's existing graded/cochain/derived
instance caches, again with the identical constructions, and caches its generic
cochain and derived monoidal structures by inferInstance. This avoids repeating
the same instance construction in the generic binary calculations.

## Old

```lean
universe u v w
```

The module had no `first_generic` or `second_generic` helpers, nor local caches for
its graded tensor, cochain monoidal, derived monoidal, or Q lax monoidal instances.

## New

```lean
universe u v w u' v'
```

`first_generic` and `second_generic` are private, fully proved categorical lemmas.
Local instances cache `GradedObject.HasTensor`, `HasTensor₄ObjExt`,
`HasGoodTensor₁₂Tensor`, `HasGoodTensorTensor₂₃`, `CochainComplex.HasMapBifunctor`,
the existing cochain monoidal
structure, `schemeDerivedTensorMonoidal X`, and the Q lax monoidal structure
`Functor.LaxMonoidal.ofIso (DerivedCategory.quotientCompQhIso _)`.
All are the existing constructions, definitionally unchanged. They introduce no
new global instance registrations or public signature changes. Unused-variable
linting is scoped off for the original hypotheses that the shorter proofs do not need.

## Users

The local instance registrations and private proof helpers have no effect on
importers. No other module is adapted. All public declarations keep their signatures.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SchemeTensorShiftLocalizationNormalization | K4 | Complete normalization calculations using one binary localization square. |

The static checker conservatively treats the local anonymous cache signatures as
interface mentions. These users do not require any adaptation:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedMonoidalPullbackUnitalShiftKFlatOne | unclaimed | None; local cache registrations do not escape their module. |
| Sheaf.AlgebraicGeometry.DerivedPullbackCanonicalTensorShiftOne | unclaimed | None; existing signatures and constructions unchanged. |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorShiftKFlatOne | unclaimed | None; existing signatures and constructions unchanged. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociatorKFlatOne | unclaimed | None; same normalization API and comparison definitions. |

| Sheaf.AlgebraicGeometry.PerfectImmersionTensorAcrossUniverses | unclaimed | None; the new local cache only stores existing total-tensor existence proofs, and no local registration escapes its module. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | None; the new local cache only stores existing total-tensor existence proofs, and no local registration escapes its module. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | None; the new local cache only stores existing total-tensor existence proofs, and no local registration escapes its module. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | None; the new local cache only stores existing total-tensor existence proofs, and no local registration escapes its module. |

## Status

landed 20261014T004107-L-2836183 2026-10-14 (merge of deliver/K4/Sheaf.AlgebraicGeometry.SchemeTensorShiftLocalizationNormalization)
