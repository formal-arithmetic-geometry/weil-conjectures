# AlgebraicGeometry.fppf_family_isEffective_of_affine_singletons

## Reason

The proof restricts abstract pseudofunctor descent data to a small covering subfamily.
Its private restriction constructions need independent category universes and `Opposite.op`.
Preflight classifies the additional `universe` parameters and `open Opposite` command as
an interface change. This record documents those commands. No existing declaration,
definition, instance, attribute, or public import changes; in particular the public theorem
signature is byte-for-byte unchanged. The additional universes occur only in private helpers.
An `open` command resolves names within this file and adds no exported declaration or instance.
All private data constructions have complete bodies, and both private theorems are proved.
No target statement or definition changes meaning and no downstream adaptation is needed.

## Old

```lean
universe u

open CategoryTheory CategoryTheory.Limits
```

## New

```lean
universe u v w v' w'

open CategoryTheory CategoryTheory.Limits Opposite
```

The public theorem remains `AlgebraicGeometry.fppf_family_isEffective_of_affine_singletons`
with exactly its existing signature. The three public imports remain verbatim. All added
imports are private proof imports. The docstring and DAG proof now describe the small-cover
universe reduction as well as the original affine-refinement assembly.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FppfFamilyAffineEffectivityReduction
--uses fppf_family_isEffective_of_affine_singletons` reports one downstream consumer.
The item's own textual occurrence is the theorem declaration itself. There are 31 transitive
importers, whose public environment and available signatures are unchanged. None uses a new
private helper or requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SecTraceFormula.SeparatedLqfFppfEffectiveDescent | unclaimed | Same theorem signature and public imports; its application at line 94 is unchanged. |

## Status

landed 20261023T135035-L-2828610 2026-10-23 (merge of deliver/M4/Sheaf.AlgebraicGeometry.FppfFamilyAffineEffectivityReduction)
