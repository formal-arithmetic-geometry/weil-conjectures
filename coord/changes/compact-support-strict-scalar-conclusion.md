# WeilConjectures.PurStrictScalar.compactSupportStrictScalarMate

## Reason

Earlier runs reported 22--24 seconds of end-of-file processing under the profiler
label `linting`, after the final expanded theorem header elaborated in less than
one second. Together with the existing finite
derived balancing declarations this exceeds the 60-second per-file budget.
The conclusion is now named by a transparent abbreviation. Its body is copied
verbatim from the original conclusion; the theorem keeps all its original binders,
including all the explicitly included finite-field and geometric assumptions.
This is a definitional presentation change, with no change of mathematical statement.
The resulting main file compiled successfully in 51.4 seconds during profiling;
all diagnostic settings are removed before delivery.
No target statement or existing definition is changed. No linter is disabled.

## Old

```lean
theorem compactSupportStrictScalarMate (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) :
    IsIso (Functor.whiskerLeft (finiteTorConstructibleIntegral l E X).ι
      (arrow l E F i c S S' e he hepos)) ∧
    ∀ (M : DerivedCategory (scalarReductionSource l E X))
      (_hM : finiteTorConstructibleIntegral l E X M),
      (∀ n : ℕ,
        (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Y n).map
            ((arrow l E F i c S S' e he hepos).app M) ≫
            (targetEvaluation l E F i c S' e he hepos n).hom.app M =
          (sourceEvaluation l E F i c S e he hepos n).hom.app M ≫
            (positiveRestriction l F Y (e * (n + 1))
              (Nat.mul_pos hepos (Nat.le_add_left 1 n))).map
              (PurCompactSupport.finiteTensorMap l E F i e he hepos n c M)) ∧
      (∀ n : ℕ, IsIso (PurCompactSupport.finiteTensorMap l E F i e he hepos n c M)) ∧
      ∀ (a b : ℕ) (hab : a ≤ b),
        (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Y b).map
            ((arrow l E F i c S S' e he hepos).app M) ≫
            (pbcTowerTransition Y ((constants l F).ring Y) b a hab).app
              ((support l F c S' ⋙ subsequence l F Y e).obj
                ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) =
          (pbcTowerTransition Y ((constants l F).ring Y) b a hab).app
              ((support l E c S ⋙ T l E F i Y).obj M) ≫
            (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Y a).map
              ((arrow l E F i c S S' e he hepos).app M)
```

## New

```lean
abbrev compactSupportStrictScalarMateConclusion
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) : Prop :=
    IsIso (Functor.whiskerLeft (finiteTorConstructibleIntegral l E X).ι
      (arrow l E F i c S S' e he hepos)) ∧
    ∀ (M : DerivedCategory (scalarReductionSource l E X))
      (_hM : finiteTorConstructibleIntegral l E X M),
      (∀ n : ℕ,
        (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Y n).map
            ((arrow l E F i c S S' e he hepos).app M) ≫
            (targetEvaluation l E F i c S' e he hepos n).hom.app M =
          (sourceEvaluation l E F i c S e he hepos n).hom.app M ≫
            (positiveRestriction l F Y (e * (n + 1))
              (Nat.mul_pos hepos (Nat.le_add_left 1 n))).map
              (PurCompactSupport.finiteTensorMap l E F i e he hepos n c M)) ∧
      (∀ n : ℕ, IsIso (PurCompactSupport.finiteTensorMap l E F i e he hepos n c M)) ∧
      ∀ (a b : ℕ) (hab : a ≤ b),
        (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Y b).map
            ((arrow l E F i c S S' e he hepos).app M) ≫
            (pbcTowerTransition Y ((constants l F).ring Y) b a hab).app
              ((support l F c S' ⋙ subsequence l F Y e).obj
                ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) =
          (pbcTowerTransition Y ((constants l F).ring Y) b a hab).app
              ((support l E c S ⋙ T l E F i Y).obj M) ≫
            (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Y a).map
              ((arrow l E F i c S S' e he hepos).app M)

theorem compactSupportStrictScalarMate (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) :
    compactSupportStrictScalarMateConclusion l E F i c S S' e he hepos
```

## Users

`tools/downstream.py Sheaf.Paper.CompactSupportStrictScalarMate --uses
WeilConjectures.PurStrictScalar.compactSupportStrictScalarMate` found only the
item's own declaration. The 17 importing modules contain no reference to this
name. The abbreviation is reducible, so the old and new result types are
definitionally equal and no consumer adaptation is required. The independent
reader can compare the abbreviation body with the old conclusion literally.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactSupportStrictScalarMate | Q6 | The final conclusion is folded into a transparent abbreviation; all hypotheses and conjuncts are preserved. |

## Status

landed 20261026T023838-L-607497 2026-10-26 (merge of deliver/Q6/Sheaf.Paper.CompactSupportStrictScalarMate)
