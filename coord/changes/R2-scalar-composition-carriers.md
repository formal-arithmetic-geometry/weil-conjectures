# Explicit native carriers in scalar-map composition

## Reason

The coefficient-line composition statement equates maps with outputs that carry
restriction of scalars from different source fields. Their underlying target is the
same native M-line. Comparing the two restricted module carriers makes Lean unfold
the completed coefficient-ring limit construction. An isolated statement check took
about 19 seconds in the kernel. Explicit identity functions on the native carriers
reduced this to 2.2 seconds. No mathematical assertion or definition changes.

## Old

```lean
    (twistScalarMaps ℓ E S M (κ.comp ι) m).val.app U x =
      (twistScalarMaps ℓ L S M κ m).val.app U
        ((twistScalarMaps ℓ E S L ι m).val.app U x)
```

## New

```lean
    (@id ((integralTwistLine ℓ M S m).val.obj U)
      ((twistScalarMaps ℓ E S M (κ.comp ι) m).val.app U x)) =
      (@id ((integralTwistLine ℓ M S m).val.obj U)
        ((twistScalarMaps ℓ L S M κ m).val.app U
          (@id ((integralTwistLine ℓ L S m).val.obj U)
            ((twistScalarMaps ℓ E S L ι m).val.app U x))))
```

Every binder stays verbatim. Each inserted `id` reduces to its argument. Thus the
old and new propositions are definitionally equal, with identical hypotheses,
normalizations, and conclusion. No DAG statement or target statement changes.
The proof builds the composite using Mathlib's abstract scalar-restriction composition
isomorphism, avoiding a separate linearity construction over completed rings.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientTwistsDetailed | R2 | Proves the theorem; adds carrier identities |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | Same definitionally equal theorem |
| Sheaf.Paper.PointTateFiberCanonicalComparisons | unclaimed | Same definitionally equal theorem |

The two external Lean consumers use the same declaration with exactly the same
arguments. They need no adaptation because the type is definitionally unchanged.
No source-library declaration is edited. No public attribute changes.

## Status

landed 20261026T002350-L-80243 2026-10-26 (merge of deliver/R2/Sheaf.Paper.CoefficientTwistsDetailed)
