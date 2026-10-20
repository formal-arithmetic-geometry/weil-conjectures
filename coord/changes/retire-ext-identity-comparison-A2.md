# CategoryTheory.Abelian.Ext.exactFunctorIdentityComparisonSheaf

## Reason

Retire the duplicate Sheaf theorem and its module. The adopted source module
`WeilConjectures.CategoryTheory.ExtExactFunctorIdentityComparison` already proves
`CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison` with exactly the same
universes, hypotheses, and conclusion. Its proof and all source-library declarations,
attributes, public imports, and definitions are preserved verbatim.

Only one current module imports the Sheaf duplicate, as checked by
`tools/downstream.py Sheaf.CategoryTheory.ExtExactFunctorIdentityComparison --uses
CategoryTheory.Abelian.Ext.exactFunctorIdentityComparisonSheaf` and searches of both
Lean roots. Redirect that caller and the existing DAG node to the canonical theorem.
The private helper in the retired Sheaf module has no callers; the upstream private
helper remains available to HigherDirectImageRawPullbackIdentity.

## Old

In `Sheaf.CategoryTheory.ExtExactFunctorIdentityComparison`:

```lean
theorem exactFunctorIdentityComparisonSheaf
    {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]
    (F : C ⥤ C) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 C) {X Y : C} {n : ℕ} (x : Ext.{w} X Y n) :
    (x.mapExactFunctor F).comp (Ext.mk₀ (e.hom.app Y)) (add_zero n) =
      (Ext.mk₀ (e.hom.app X)).comp x (zero_add n)
```

## New

The Sheaf module is withdrawn, with no declarations left. Use the existing theorem
in `WeilConjectures.CategoryTheory.ExtExactFunctorIdentityComparison`:

```lean
theorem exactFunctorIdentityComparison
    {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]
    (F : C ⥤ C) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 C) {X Y : C} {n : ℕ} (x : Ext.{w} X Y n) :
    (x.mapExactFunctor F).comp (Ext.mk₀ (e.hom.app Y)) (add_zero n) =
      (Ext.mk₀ (e.hom.app X)).comp x (zero_add n)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ExtExactFunctorIdentityComparison | A2 | Withdraw duplicate; attach its node to the existing upstream theorem. |
| Sheaf.AlgebraicGeometry.ScalarAbelianExtFactorization | V2 | Forced adaptation: line 10 imports the upstream module, and line 160 uses exactFunctorIdentityComparison. No signature, visibility, data, or other proof line changes. The existing local-instance signature at original line 30 is wrapped without token changes because deliver3.py refuses its pre-existing length warning. |

With the item replaced by an empty module, the original consumer fails at
`ScalarAbelianExtFactorization.lean:160:16`:

```text
error(lean.unknownIdentifier): Unknown constant `CategoryTheory.Abelian.Ext.exactFunctorIdentityComparisonSheaf`
```

The replacement theorem has the identical statement, so the consumer's theorem
retains its meaning. No target statement or definition is changed. The consumer's
pre-existing long line at line 30 is wrapped without changing any tokens: the
first dry run refused that warning despite successful compilation. This
formatting change is required by the delivery gate and 100-character rule.

## Status

landed 20261020T145443-L-2396077 2026-10-20 (merge of deliver/A2/Sheaf.CategoryTheory.ExtExactFunctorIdentityComparison)
