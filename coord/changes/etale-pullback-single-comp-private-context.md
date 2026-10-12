# Etale.upperStarPlusComp_single private proof context

## Reason

The proof uses seven private helpers for generic exact functors. The static
interface scanner flags the added namespace, variable, and omit commands and the
scoped linter setting as an interface change. This record documents those commands
for independent review. They introduce no exported declaration, notation,
attribute, instance, or changed public signature. No definition changes.

## Old

The original file has, after the existing open commands:

```lean
namespace AlgebraicGeometry
variable (Λ : Type (u + 1)) [CommRing Λ]
```

## New

Before that unchanged namespace and variable command, the proof now has:

```lean
namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
```

Seven `private lemma` declarations follow, and the namespace closes with:

```lean
end CategoryTheory.Functor
```

The generic variables are confined to this namespace. The two complex-level
helpers explicitly omit unused `HasDerivedCategory` instances. A
`set_option linter.flexible false in` scopes the linter setting to `single_hom`,
whose proof expands the comparison and then rewrites its identity component.
It changes no mathematical assumption or kernel setting.

The signature and visibility of `AlgebraicGeometry.Etale.upperStarPlusComp_single`
remain identical. All helper bodies are proved; none contains sorry.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtalePullbackSingleComp | A2 | Seven private proof helpers; unchanged public signature |
| All importers | unchanged | No public signature, definition, import, notation, or instance changes; no adaptation needed |

No public definition or statement has changed, so no dependent module needs
adaptation or renewed target-statement review. Only the item's module is edited.

## Status

landed 20261012T135214-L-1654653 2026-10-12 (merge of deliver/A2/Sheaf.AlgebraicGeometry.EtalePullbackSingleComp)
