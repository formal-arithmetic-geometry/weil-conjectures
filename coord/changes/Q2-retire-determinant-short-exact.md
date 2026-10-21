# AlgebraicGeometry.Scheme.Modules.determinant_shortExact

## Reason

Retire the duplicate listed at coord/retire-items.tsv:1725 under the human's
coord/changes/retire-sheaf-twins-20261020.md hand-off. The current item has zero
holes, no current rework row, and no return entry. Its adopted twin is already
fully proved, with the same hypotheses, three invertibility clauses, and unique
canonical determinant isomorphism characterized on every open and arbitrary
quotient lifts. It uses exteriorPower and wedge in place of the legacy
exteriorSheaf and exteriorSheafSection. No adopted source file is changed.

The sole direct consumer is Sheaf.AlgebraicGeometry.DeterminantDualEvaluation.
It needs only the middle invertibility clause at ranks 0,d,d. Replace its private
import by the adopted module; first obtain invertibility of exteriorPower M d,
then apply IsInvertible.of_iso to (exteriorSheafPowerIso M d).symm. This gives
invertibility of precisely the original F = exteriorSheaf M d. All public
imports, declarations, signatures, visibility and definitions in the consumer
remain unchanged. Its existing comparison import is sufficient.

A scratch compile of the original consumer with only the import migrated fails
at line 73: the extracted clause has type (S.X2.exteriorPower d).IsInvertible,
but F.IsInvertible is expected. The two-step adaptation compiles cleanly. The
consumer is unclaimed, and its edits are limited to this necessary API transport.
The unchanged transitive consumer ShiftedDeterminantDualEvaluation times out
at 60 seconds both against the adapted consumer and against the original
published baseline. Profiling also times out without returning diagnostics.
No change to that transitive file is delivered; the direct consumer compiles.

Retain lem-sc-determinant-short-exact with its Lean attachment on the adopted
theorem and its complete verbatim adopted signature. Its proof record now follows
the adopted proof: the proved local-frame invertibility instance, determinant
existence, and uniqueness from lifted-wedge extensionality. The legacy comparison
is no longer needed inside this node; its consumer's node explicitly records
transport of the invertibility clause. The Riemann--Roch parent also cites this
node; its existing determinant argument remains valid with the canonical exterior
power representation, so that parent requires no change. All DAG nodes remain.
This preserves the unit's determinant multiplicativity step.

The isomorphism transport works for d=0, empty opens, the empty scheme and zero
section rings: it adds no hypothesis and uses a genuine comparison isomorphism.
No arbitrary data is chosen from a mere existence statement. No target statement
or definition changes and no hole is added.

## Old

```lean
theorem determinant_shortExact {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₂.IsFiniteLocallyFreeOfRank r₂]
    [S.X₃.IsFiniteLocallyFreeOfRank r₃] :
    (exteriorSheaf S.X₁ r₁).IsInvertible ∧
    (exteriorSheaf S.X₂ r₂).IsInvertible ∧
    (exteriorSheaf S.X₃ r₃).IsInvertible ∧
    ∃! e : exteriorSheaf S.X₂ r₂ ≅ exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃,
      ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        e.inv.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₃ r₃ U b)) =
          exteriorSheafSection S.X₂ r₂ U
            (fun i => Fin.append (fun j => S.f.val.app (op U) (a j)) c (Fin.cast hr i))
```

## New

Withdraw the legacy duplicate via deleted.txt. Its adopted replacement, unchanged,
in WeilConjectures.AlgebraicGeometry.Modules.DeterminantShortExact is:

```lean
theorem determinant_shortExact {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₂.IsFiniteLocallyFreeOfRank r₂]
    [S.X₃.IsFiniteLocallyFreeOfRank r₃] :
    (exteriorPower S.X₁ r₁).IsInvertible ∧
    (exteriorPower S.X₂ r₂).IsInvertible ∧
    (exteriorPower S.X₃ r₃).IsInvertible ∧
    ∃! e : exteriorPower S.X₂ r₂ ≅ exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃,
      ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        e.inv.val.app (op U)
          (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
            (wedge (M := S.X₃) (r := r₃) (U := U) b)) =
          wedge (M := S.X₂) (r := r₂) (U := U)
            (fun i => Fin.append (fun j => S.f.val.app (op U) (a j)) c (Fin.cast hr i))
```

The unchanged consumer signature still uses exteriorSheaf; its proof transfers
only the middle invertibility clause through exteriorSheafPowerIso.

## Users

The downstream scan reports the direct consumer and its single transitive
consumer. Current claim files show neither consumer held by a group.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | Q2 | Retire duplicate and retain its node on the adopted theorem. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Migrate private import and transport invertibility; public interface preserved verbatim. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Unchanged transitive consumer; baseline and overlay checks both time out at 60 seconds (pre-existing). |
| WeilConjectures.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Adopted replacement; unchanged. |

## Status

landed 20261021T111434-L-136588 2026-10-21 (merge of deliver/Q2/Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact)
