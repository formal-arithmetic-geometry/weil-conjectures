# AlgebraicGeometry.Scheme.nonempty_sheafH_extDerivedIso

## Reason

The direct comparison proof requires private helpers for cochain postcomposition,
cohomology-class naturality and the termwise global-sections identification. The
preflight interface detector classifies added `open` and `variable` commands as
an interface change even though they are local to this file and all added
declarations are private. This record documents the commands instead of changing
or bypassing that check. No existing definition, instance, attribute, public
import or theorem statement is changed.

## Old

The existing theorem signature, verbatim:

```lean
theorem nonempty_sheafH_extDerivedIso (X : Scheme.{u}) (q : ℕ) :
    Nonempty (Sheaf.functorH.{u + 1} X.smallEtaleTopology q ≅
      DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} X (q : ℤ))
```

The file originally had `universe u`, `open CategoryTheory`, and namespace
`AlgebraicGeometry.Scheme`, with no auxiliary namespace or variable commands.

## New

The existing theorem signature, verbatim and unchanged:

```lean
theorem nonempty_sheafH_extDerivedIso (X : Scheme.{u}) (q : ℕ) :
    Nonempty (Sheaf.functorH.{u + 1} X.smallEtaleTopology q ≅
      DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} X (q : ℤ))
```

The following commands now scope private proof helpers in `EtaleComparisonAux`:

```lean
open CochainComplex HomComplex Limits
universe v w
variable {C : Type w} [Category.{v} C] [Preadditive C]
  {S K L : CochainComplex C ℤ}
```

A separately scoped reopening of that namespace uses:

```lean
open CochainComplex HomComplex Limits
universe v w
variable {C : Type w} [Category.{v} C] [Abelian C] [HasExt.{v} C]
```

Inside `AlgebraicGeometry.Scheme` the proof helpers use:

```lean
open CochainComplex HomComplex Limits Opposite
```

These commands add no notation or instances to importing modules. The fully proved
private declarations use only standard axioms. The proof-only imports are
`Mathlib.CategoryTheory.Abelian.Injective.Ext` and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`.
No target statement or definition used by a target changes its meaning.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
--uses nonempty_sheafH_extDerivedIso` lists 100 downstream modules and the
following two modules mentioning this declaration. No user requires adaptation:
all public types, names and imports are preserved, and no instance is added.
The static scope-command placeholder itself occurs in no downstream source.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison | M1 | Completes its proof; same signature. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | Not adapted in this delivery | Existing two applications keep the same type and acquire the completed proof. |

## Status

landed 20261012T012858-L-817697 2026-10-12 (merge of deliver/M1/Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison)
