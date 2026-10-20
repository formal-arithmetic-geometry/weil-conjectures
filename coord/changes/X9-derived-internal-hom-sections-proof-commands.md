# Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel

## Reason

Preflight classifies added section commands as an interface change. This record covers the
proof-local namespaces, opens, `omit`, and local irreducibility attribute used to prove
`CategoryTheory.DerivedInternalHomSectionsModel.derived_internalHom_sections_model`.
They keep elaboration behind existing APIs. The existing public signatures, definitions,
attributes and public imports are unchanged; no target meaning changes.

## Old

There was no `CategoryTheory.DerivedInternalHomSectionsModel.GlobalCochains` helper
namespace, no proof-local `omit` command, and no local irreducibility command.
The surrounding existing namespace command, verbatim, is:

```lean
namespace CategoryTheory.DerivedInternalHomSectionsModel
```

## New

The added private helper namespace is closed before reopening the existing namespace:

```lean
namespace CategoryTheory.DerivedInternalHomSectionsModel.GlobalCochains
```

Its three helper declarations use the scoped command:

```lean
open CochainComplex HomComplex Limits Preadditive in
```

After the unchanged tensor-adjoint theorem, the proof uses:

```lean
attribute [local irreducible] derivedInternalHomOfUniverses homComplexFunctor

omit [HasDerivedCategory.{w} (Modules.{c, v, r} R)]
  [HasDerivedCategory.{z} AddCommGrpCat.{max c v r}] in
```

The next private comparison additionally uses:

```lean
omit [HasDerivedCategory.{z} AddCommGrpCat.{max c v r}] in
```

All these commands are scoped to this file or individual private declarations. They export
no new instance, notation or attribute. New helpers are private and fully proved.
The separately recorded new module
`Sheaf.Algebra.Homology.GlobalTensorHomCochainsOfUniverses` exports only the proved
`CategoryTheory.global_tensorHom_cochainsOfUniverses` theorem; its node records its statement.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel --uses
derived_internalHom_sections_model tensorRightAdjoint_iso` finds the following declaration
users. The only external hit uses the first theorem twice with its unchanged signature.
All 893 transitive importers see the same existing public interface. No consumer adaptation
is necessary because the added commands are local and existing declarations are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel | X9 | Original theorem proved; local proof commands added. |
| Sheaf.Algebra.Homology.RhomHypercohomologyBridgeOfUniverses | unclaimed | Uses unchanged theorem signature; no adaptation. |
| Sheaf.Algebra.Homology.GlobalTensorHomCochainsOfUniverses | X9 (new) | Proved supporting theorem; no existing consumer changes. |

## Status

landed 20261020T211900-L-3514092 2026-10-20 (merge of deliver/X9/Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel)
