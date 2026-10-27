# Completed pullback tensor counit components

## Reason

Prove the three actual counit isomorphisms needed by the integral pullback/tensor
comparison using the existing normalized reconstruction and transported reduction
interfaces. Separate tensor and single-input pullback lemmas make the argument
reusable and avoid duplicating the normalization proof for the two inputs.

## Old

The two new helper modules and their declarations were absent.
`pullbackTensorComparisonCounits` had the same signature and proof `by sorry`.

## New

The existing parent signature is unchanged. It assembles the two component
lemmas below, with the pullback lemma applied to each input. Both helpers are
proved from existing declarations; no new proof obligations are introduced.

```lean
theorem completedPullbackTensor_tensor_counit
    (W : Scheme.{u}) (_hW : ∀ w : W, IsUnit (l : W.residueField w))
    (C : CoefficientDerivedSystemCalculus l E W)
    (M N : DerivedCategory (scalarReductionSource l E W)) :
    IsIso (C.adjunction.counit.app
      (C.systemClosed.tensor.obj (C.reduction.obj M, C.reduction.obj N)))
```

```lean
theorem completedPullbackTensor_pullback_counit
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_hX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hY : ∀ y : Y, IsUnit (l : Y.residueField y))
    (C : CoefficientDerivedSystemCalculus l E X)
    (D : CoefficientDerivedSystemCalculus l E Y)
    (G : coefficientSequenceModules l E Y ⥤ coefficientSequenceModules l E X)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (hG : G = integralComparisonSequencePullback l E f)
    (M : DerivedCategory (scalarReductionSource l E Y)) :
    IsIso (C.adjunction.counit.app
      ((G.mapDerivedCategory).obj
        (D.reduction.obj M)))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | J3 | Two private proof imports; assembles component isomorphisms. |

Both component modules are new and have no pre-existing consumers. No existing
signature, attribute, or public import is changed by the counit component proof.
The definitionally equal normalization refactor is recorded separately in
`j3-completed-pullback-tensor-normalization-cache.md`. The component lemmas
have only the item module as consumer; no forced adaptations are needed.

## Status

landed 20261026T070030-L-3344536 2026-10-26 (merge of deliver/J3/Sheaf.Paper.CompletedPullbackTensorComparison)
