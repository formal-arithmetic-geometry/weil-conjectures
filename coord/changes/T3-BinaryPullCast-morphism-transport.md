# WeilConjectures.CompactSupportFiniteProjection.binaryPullCast

## Reason

At object components, comparing the original equality transport with the
triangle's transport caused a deterministic kernel timeout. The generic
natural-isomorphism cancellation checks quickly, while its concrete component
comparison unfolds equality transport on entire derived functors.

Use `morphismPullbackCongr`, constructed by induction on the indexing morphism
equality. Its proved theorem `morphismPullbackCongr_eq` identifies it with the
original `Calculus.pCongr` for every calculus and equality. The source library's
`leftDerivedUpperStarCongr` uses the same morphism-induction construction to
avoid comparing large derived functors inside `eqToIso`.

The binders, inferred result type, visibility, and specified comparison map are
unchanged. The new construction requires the added public import
`Sheaf.SixFunctors.PullbackEqualityTransport`. Definitions used by targets are
subject to renewed statement review; the proved generic equality certifies that
this change preserves the comparison and therefore its meaning.

## Old

```lean
def binaryPullCast (A : Type (u + 1)) [CommRing A] [Finite A] :=
  (ordinary D A).pCongr (show (j ≫ q) ≫ (i ≫ s) = (j ≫ b) ≫ (p ≫ s) by
    simp only [Category.assoc]
    rw [← Category.assoc q i s, ← hb]
    simp only [Category.assoc])

```

## New

```lean
def binaryPullCast (A : Type (u + 1)) [CommRing A] [Finite A] :=
  morphismPullbackCongr (ordinary D A) (show (j ≫ q) ≫ (i ≫ s) = (j ≫ b) ≫ (p ≫ s) by
    simp only [Category.assoc]
    rw [← Category.assoc q i s, ← hb]
    simp only [Category.assoc])

```

## Users

The declaration-name search lists only the defining module. The three direct
importers are also checked because they use comparisons defined in that module.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.FiniteProjectionCompositionRealization` | T3 | Same equality transport through the proved morphism-indexed constructor. |
| `Sheaf.Paper.FiniteProjectionBinaryIterationTrianglePasting` | unclaimed | Check the original source against the changed definition. |
| `Sheaf.Paper.FiniteProjectionBinaryTriangleSquare` | unclaimed | Add a proved private adapter and change the total-factor calculation to use it; keep every existing signature. |
| `Sheaf.Paper.FiniteProjectionBinarySquare` | unclaimed | Check the original source against the changed definition. |
| `Sheaf.Paper.FiniteProjectionCompositionData` | T3 | Preserve the coordinate definitions and endpoint structure under their original names. |
| `Sheaf.Paper.FiniteProjectionCompositionEndpointProofs` | T3 | Check the source and tensor endpoint normalizations. |

## Module split

The existing public coordinate definitions, their hom formulas, and
`BinaryCompositionRealization` are relocated verbatim into the new module
`Sheaf.Paper.FiniteProjectionCompositionData`. The item publicly imports that
module, preserving all existing declaration names and signatures for its users.
Their DAG declaration attachment is moved to
`def-sf-finite-projection-composition-data`; the original node retains the final
normalization theorem. This separates the expensive checking of the original
endpoint structure from the checking of its proof.

## Forced consumer adaptation

The original `FiniteProjectionBinaryTriangleSquare` fails against this packet at
`total_component_realization` (original line 197):

```text
error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

Its application of `scalar_factor_realization` supplies `pCongr` while the
prescribed `binaryTargetComparison` now uses `morphismPullbackCongr`. Add the
proved private `scalar_factor_realization_morphism`, with the same input data and
the morphism-indexed transport in its conclusion. Its proof eliminates `hf` and
applies the unchanged original helper at reflexivity, where both transports are
the identity. Change only the callee in `total_component_realization` to this
adapter. Every existing declaration signature remains identical, including the
original private helper. The module is unclaimed in the current claim records.
The adapted module and its direct importer `FiniteProjectionBinarySquare` are
checked against the packet.

## Status

landed 20261028T055804-L-809833 2026-10-28 (merge of deliver/T3/Sheaf.Paper.FiniteProjectionCompositionRealization)
