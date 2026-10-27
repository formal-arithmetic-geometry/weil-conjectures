# WeilConjectures.PurityFiniteSetting.exists_finiteReductionSourceChartScalar

## Reason

Isolate the arithmetic transition between primitive-root charts needed to construct
the existing root-independent base-change source map. The original square-map
existence and uniqueness are proved by combining this substep with categorical
scalar cancellation and existence of a primitive root.

## Old

No declaration with this name or this uniform scalar statement existed. The
containing item had three named sorry proofs; all existing signatures, public
imports and data definitions are preserved verbatim.

## New

A new public theorem in `Sheaf.Paper.FiniteSourceChartScalarTransition`:

```lean
theorem exists_finiteReductionSourceChartScalar (P : PurityFiniteSetting.{u})
    (d : ℕ) (ζ η : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hη : IsPrimitiveRoot η P.diagonalExponent) :
    ∃ r : ℕ, ∀ {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
      (f : X ⟶ Y) (K : Scheme.proEtaleDerivedCategory Y P.Ring),
      (P.finiteReductionSourceTrivialization f d ζ hζ K).inv ≫
        (P.finiteReductionSourceTrivialization f d η hη K).hom =
          r • 𝟙 (((P.finiteReductionPullback f).obj K)⟦2 * (d : ℤ)⟧)
```

Its whole proof is `by sorry`, with the complete arithmetic proof in its docstring
and its own node. No data are selected from this mere existence theorem: the
proved parent uses the scalar only within a propositional proof. The existing
source-map data continue to be selected from the parent's unique specification.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | New private proof import; existing statements and definitions unchanged. |

The new module has no pre-existing users. The item imports it only for its proof;
its consumers see precisely the existing public interface. No consumer adaptation
or target-statement change is needed.

## Status

landed 20261025T101650-L-3720342 2026-10-25 (merge of deliver/V6/Sheaf.Paper.FiniteSmoothPullbackExchange)
