# CategoryTheory.Functor.leftDerived_exact_when_defined

## Reason

The custom IsStrictLocalizationAt predicate has two fixed test-category universe parameters.
It states strict factorization and bijectivity only for targets at those universe levels.
The theorem elaborates with two additional unconstrained universe parameters for this predicate;
it does not provide the Mathlib Q.IsLocalization S instance needed to use fraction calculus,
pointwise Kan limits on the localization, or the 05R6 triangle-image statement.
The paper already assumes that Q is an abstract localization. Record that assumption directly
as [Q.IsLocalization S]. Retain the original strict predicate for source compatibility and
rename its now-unused binder to _hQ. This is an intermediate theorem, not a Challenge target.
The mathematical DAG statement already requires an abstract localization and is unchanged.

## Old

```lean
theorem leftDerived_exact_when_defined (D : Type u) [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [CategoryTheory.IsTriangulated D] (D' : Type u') [Category.{v'} D'] [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D'] [CategoryTheory.IsTriangulated D'] (L : Type u'') [Category.{v''} L] [HasZeroObject L] [HasShift L ℤ] [Preadditive L] [∀ n : ℤ, (shiftFunctor L n).Additive] [Pretriangulated L] [CategoryTheory.IsTriangulated L] (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated] (S : MorphismProperty D) (hS : S.IsSaturatedTriangulatedMultiplicativeSystem) (Q : D ⥤ L) [Q.CommShift ℤ] [Q.IsTriangulated] (hQ : Q.IsStrictLocalizationAt S) (LF : L ⥤ D') (α : Q ⋙ LF ⟶ F) (hLF : LF.IsRightKanExtension α) (hdefined : ∀ X : D, F.IsTriangulatedLeftDerivedDefinedAt S hS X) : ∃ (_ : LF.CommShift ℤ), LF.IsTriangulated
```

## New

```lean
theorem leftDerived_exact_when_defined (D : Type u) [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [CategoryTheory.IsTriangulated D] (D' : Type u') [Category.{v'} D'] [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D'] [CategoryTheory.IsTriangulated D'] (L : Type u'') [Category.{v''} L] [HasZeroObject L] [HasShift L ℤ] [Preadditive L] [∀ n : ℤ, (shiftFunctor L n).Additive] [Pretriangulated L] [CategoryTheory.IsTriangulated L] (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated] (S : MorphismProperty D) (hS : S.IsSaturatedTriangulatedMultiplicativeSystem) (Q : D ⥤ L) [Q.CommShift ℤ] [Q.IsTriangulated] [Q.IsLocalization S] (_hQ : Q.IsStrictLocalizationAt S) (LF : L ⥤ D') (α : Q ⋙ LF ⟶ F) (hLF : LF.IsRightKanExtension α) (hdefined : ∀ X : D, F.IsTriangulatedLeftDerivedDefinedAt S hS X) : ∃ (_ : LF.CommShift ℤ), LF.IsTriangulated
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.DerivedCategory.LeftDerivedExactOfLocalization | none | Its existing constructed-localization instance infers the new binder; its original source was compiled unchanged against the delivery. Its theorem statement and behavior are unchanged. |

The downstream --uses scan found this sole external caller (plus the declaration itself).
The remaining 622 import descendants do not mention the declaration and require no adaptation.
No target definition or target statement changes, so there is no target meaning change to reopen.

## Status

landed 20261012T135328-L-1697773 2026-10-12 (merge of deliver/V2/Sheaf.CategoryTheory.LeftDerivedExactWhenDefined)
