# pullback_stalk_relative_flat_extension

## Reason

The preflight conservatively flags the new open, section, variable and omit
commands used to prove private helpers as an interface change. All helpers are
private, all three added imports are proof-only, and the existing theorem's
signature and public imports are identical. No definition used by a target changes.
The TensorProduct opens are elaboration scopes, not exported declarations.

## Old

```lean
theorem pullback_stalk_relative_flat_extension
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) (z : ↥(pullback f p))
    (M : ModuleCat.{u} (X.presheaf.stalk ((pullback.fst f p) z)))
    (hM : Module.Flat (S.presheaf.stalk (f ((pullback.fst f p) z)))
      ((ModuleCat.restrictScalars (f.stalkMap ((pullback.fst f p) z)).hom).obj M)) :
    Module.Flat (T.presheaf.stalk ((pullback.snd f p) z))
      ((ModuleCat.restrictScalars ((pullback.snd f p).stalkMap z).hom).obj
        ((ModuleCat.extendScalars ((pullback.fst f p).stalkMap z).hom).obj M)) 
```

Original scopes: namespace AlgebraicGeometry with CategoryTheory and
CategoryTheory.Limits open; no helper section.

## New

```lean
theorem pullback_stalk_relative_flat_extension
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) (z : ↥(pullback f p))
    (M : ModuleCat.{u} (X.presheaf.stalk ((pullback.fst f p) z)))
    (hM : Module.Flat (S.presheaf.stalk (f ((pullback.fst f p) z)))
      ((ModuleCat.restrictScalars (f.stalkMap ((pullback.fst f p) z)).hom).obj M)) :
    Module.Flat (T.presheaf.stalk ((pullback.snd f p) z))
      ((ModuleCat.restrictScalars ((pullback.snd f p).stalkMap z).hom).obj
        ((ModuleCat.extendScalars ((pullback.fst f p).stalkMap z).hom).obj M)) 
```

Added open scoped TensorProduct, open TensorProduct, and the private helper
namespace RelativeFlatTensorExtension with section variables and omit clauses.
All added declarations are private and proved. The theorem now has a complete
proof from the existing stalk-flatness theorem and two tensor-injectivity checks.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PullbackStalkRelativeFlatExtension | M4 | Private helpers prove its theorem; unchanged public signature. |
| Sheaf.AlgebraicGeometry.RelativelyFlatModulePullback | unclaimed | The sole external textual caller; identical theorem type, no adaptation needed. |

The downstream scan reports 403 transitive importers, but only the second row
uses the declaration. None needs adaptation because the exported theorem and
public imports stay identical. There are no changes to existing definitions,
statements, universes or visibility, and no new public declarations.

## Status

landed 20261013T100036-L-2471144 2026-10-13 (merge of deliver/M4/Sheaf.AlgebraicGeometry.PullbackStalkRelativeFlatExtension)
