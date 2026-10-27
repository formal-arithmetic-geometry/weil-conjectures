# WeilConjectures.rationalTensorStageComparison_coherent

## Reason

The static interface heuristic flags added `variable`, section and `attribute`
commands in the item. They support private proof helpers. The new field variables
are scoped inside `ProofHelpers`, and all added reducibility attributes are local.
They do not change an exported signature or a global attribute.

This is a proof completion, not a definition or statement repair.
The public definition `WeilConjectures.rationalTensorStageComparison`, the theorem
signature below, and the three original public imports are unchanged. The private
helpers `tensorStageComparison_endpoint` and `tensorDescent_with_components`
are retained verbatim because the parent imports them with `import all`.
New private definitions only cache typed versions of the existing functors and
comparisons. No private helper appears in an existing public signature or the
body of an existing public definition.

## Old

```lean
theorem rationalTensorStageComparison_coherent :
    BilinearCoefficientDescent.FamilyTower (stageSystem l Ω W) (stageSystem l Ω W)
      (stageSystem l Ω W)
      (fun E ↦ rationalDerivedTensor l (Coefficient.{u} l Ω E) W)
      (fun {_ _} h ↦ rationalTensorStageComparison l Ω W h)
```

The old proof is `by sorry`.

## New

```lean
theorem rationalTensorStageComparison_coherent :
    BilinearCoefficientDescent.FamilyTower (stageSystem l Ω W) (stageSystem l Ω W)
      (stageSystem l Ω W)
      (fun E ↦ rationalDerivedTensor l (Coefficient.{u} l Ω E) W)
      (fun {_ _} h ↦ rationalTensorStageComparison l Ω W h)
```

The proof now follows the ordinary tensor tower through completion,
rationalization and recorded stage-data transport. `TensorTowerDatum.Coherent`
is the full component equation, held behind the data record while changing
category presentations. No existing data construction changes.

## Users

The only direct importer and the only other module referring to these names is
`Sheaf.Paper.DerivedPullbackTensorHom`. No consumer is adapted or delivered.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.RationalTensorStageCoherence` | N1 | Complete its proof; preserve its existing declarations. |
| `Sheaf.Paper.DerivedPullbackTensorHom` | E3 | Unchanged consumer; both imported private helpers and the public API are preserved. |

Consumer validation completed Lean checking but hit the 60-second gate at
63.9 seconds. The same unchanged parent against the original unproved item
also exceeded the gate, at 77 seconds. Neither run reported a Lean error.
The baseline run reused the cached private-overlay pullback dependencies.
The parent is therefore left untouched with E3; this proof changes no interface
that would authorize a forced adaptation. The temporary source copy was removed.

## Status

landed 20261027T123508-L-2310452 2026-10-27 (merge of deliver/N1/Sheaf.Paper.RationalTensorStageCoherence)
