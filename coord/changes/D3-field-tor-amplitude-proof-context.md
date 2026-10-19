# WeilConjectures.field_tor_amplitude

## Reason

A private helper introduces declaration-scoped namespace and elaboration commands.
The namespace opening is scoped to that helper using `open ... in`.
The helper, its local universe-size instance, and its declaration-scoped elaboration
options support the proof of the existing theorem. No existing declaration signature,
visibility, definition, or public import changes. No consumer needs adaptation and no
target statement or definition changes meaning.

## Old

The existing theorem `WeilConjectures.field_tor_amplitude` had proof `:= by sorry`.
There was no helper or additional namespace-opening command in `namespace WeilConjectures`.

## New

The existing theorem has the identical signature and a complete proof using a private
proved helper. Its helper signature and scoped commands are:

```lean
open CategoryTheory.Limits CategoryTheory.MonoidalCategory in
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem bounded_field_tor
    (Y : Scheme.{u}) (A : Type u) [Field A]
    (K : proEtaleDerivedCategory Y A) (a b : ℤ) (hab : a ≤ b)
    (hK : ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) :
    HasProEtaleTorAmplitude Y A K a b
```

The local smallness instance is `essentiallySmallSelf.{0, u, u + 1}` at exactly universe `u + 1`.
It only affects elaboration inside that proof. The helper is used only in a theorem proof,
never in a public definition or signature. Added proof imports are non-public, including `Mathlib.Algebra.Field.ULift`. The tensor comparison is a composite of existing natural isomorphisms, with a proved sectionwise identity comparison. No profiler, trace, or increased heartbeat limit remains.

## Users

`tools/downstream.py Sheaf.Paper.FieldTorAmplitude --uses
WeilConjectures.field_tor_amplitude` reports two downstream modules and only the item's
own declaration-name occurrence. Both consumers were inspected. The public theorem
signature and all public imports remain identical, so their statements and definitions
retain the same meaning. No consumer is included or adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FieldTorAmplitude | D3 | Existing proof completed; private helper added. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same interface; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Same interface; no adaptation. |

## Status

landed 20261019T132227-L-1203898 2026-10-19 (merge of deliver/D3/Sheaf.Paper.FieldTorAmplitude)
