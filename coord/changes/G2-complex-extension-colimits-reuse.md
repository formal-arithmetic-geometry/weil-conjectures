# extension_preservesColimits

## Reason

The second reading found the abelian hypercover total repeating the exact generic
private theorem from `Sheaf.AlgebraicGeometry.ProEtaleModuleCohomologyCoproducts`.
Move the existing proof unchanged into the small shared module
`Sheaf.Algebra.Homology.ComplexExtensionColimits` and import it privately in both
callers. This removes duplication without importing the full module-direct-image
framework into the abelian total. The source module is unclaimed; its historical
landing group was C2. No module held by another group is changed.

## Old

In `Sheaf.AlgebraicGeometry.ProEtaleModuleCohomologyCoproducts`:

```lean
private theorem extension_preservesColimits {C : Type u} [Category.{v} C]
    [HasZeroObject C] [HasZeroMorphisms C]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (J : Type w) [Category.{z} J] [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (e.extendFunctor C)
```

The new abelian total module contained the same statement and proof, with universe
names inferred instead of declared. Both private copies are removed.

## New

In `Sheaf.Algebra.Homology.ComplexExtensionColimits`:

```lean
theorem extension_preservesColimits {C : Type u} [Category.{v} C]
    [HasZeroObject C] [HasZeroMorphisms C]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (J : Type w) [Category.{z} J] [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (e.extendFunctor C)
```

The signature and proof are copied verbatim from the existing source, removing
only `private`. The original source module gains a plain proof import; all its
other declarations, public signatures and proof bodies are unchanged. The abelian
total gains the same plain import, removes its private copy and its now-unused
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero` import, and uses the shared
helper under its original name. The helper's source, proof and new DAG attachment
are documented in its new module. No object or target meaning changes.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleModuleCohomologyCoproducts
--uses extension_preservesColimits` found only the source module itself. Its one
transitive importer is `Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts`;
there is no downstream interface adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ProEtaleModuleCohomologyCoproducts` | unclaimed | Remove the private helper and import its unchanged proof from the shared module; all public interfaces stay identical. |
| `Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts` | unclaimed | No use of the formerly private helper; public interfaces and statements unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleAbelianHypercoverTotal` | G2, new delivery module | Remove the duplicate helper and reuse the shared proof. |
| `Sheaf.Algebra.Homology.ComplexExtensionColimits` | G2, new delivery module | New home of the existing proof. |

## Status

landed 20261016T040116-L-2417209 2026-10-16 (merge of deliver/G2/Sheaf.Paper.CondensedQcqsPushforwardLocalComparison)
