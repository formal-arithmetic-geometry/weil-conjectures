# WeilConjectures.normalizedRationalEvaluation_naturality

## Reason

The unchanged public theorem now has a complete proof. The static interface scanner
flags new top-level proof commands: a one-theorem `omit` for an unused residue-field
invertibility instance and a one-theorem `set_option maxHeartbeats 600000 in` for the
final specialization through the chosen normalized functors. Both commands have
lexical scope over their following theorem. Neither changes any public signature,
public import, definition, instance, notation, or downstream elaboration setting.
All added helper declarations are private and proved. This record documents the
conservative preflight classification; no mathematical interface repair is made.

## Old

```lean
theorem normalizedRationalEvaluation_naturality
    (P P' : (constructibleRationalHomPairs l E W).FullSubcategory) (g : P ⟶ P') :
    (rationalDerivedTensor l E W).map
        (Prod.mkHom ((rationalDerivedInternalHom l E W).map g) (𝟙 P'.obj.1.unop)) ≫
      (podRationalClosed l E W).evaluation P' =
    (rationalDerivedTensor l E W).map
        (Prod.mkHom (𝟙 ((rationalDerivedInternalHom l E W).obj P)) g.hom.1.unop) ≫
      (podRationalClosed l E W).evaluation P ≫ g.hom.2 := by
  sorry
```

## New

```lean
theorem normalizedRationalEvaluation_naturality
    (P P' : (constructibleRationalHomPairs l E W).FullSubcategory) (g : P ⟶ P') :
    (rationalDerivedTensor l E W).map
        (Prod.mkHom ((rationalDerivedInternalHom l E W).map g) (𝟙 P'.obj.1.unop)) ≫
      (podRationalClosed l E W).evaluation P' =
    (rationalDerivedTensor l E W).map
        (Prod.mkHom (𝟙 ((rationalDerivedInternalHom l E W).obj P)) g.hom.1.unop) ≫
      (podRationalClosed l E W).evaluation P ≫ g.hom.2
```

The type is verbatim unchanged. Its body derives integral evaluation naturality
from the ordinary counit and actual completion unit, normalizes rational evaluation,
and applies a proved generic bilinear-localization calculation with tensor-product
induction in both arrows. The new scoped commands are:

```lean
omit [∀ w : W, Invertible (l : W.residueField w)] in
private theorem completed_unit_natural
```

and

```lean
set_option maxHeartbeats 600000 in
-- The specialization checks the normalized object equalities of three chosen functors.
```

The latter applies only to the existing public theorem's proof elaboration.

## Users

`tools/downstream.py Sheaf.Paper.NormalizedRationalEvaluationNaturality --uses
WeilConjectures.normalizedRationalEvaluation_naturality` reports the two direct
name users below. There are eight modules in its transitive import closure; the
other six only import the same unchanged interface and need no adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | U4 | Same statement; hole closed; private proved helpers. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Same public statement and imports; no adaptation required. |

No target type or definition used by a target is changed. The scoped option is
not exported to any of these users. The delivered module passed server lcompile
with no warnings in 20.5 seconds, and passed delivery compilation before this
record was requested by server preflight.

## Status

landed 20261021T214907-L-1883356 2026-10-21 (merge of deliver/U4/Sheaf.Paper.NormalizedRationalEvaluationNaturality)
