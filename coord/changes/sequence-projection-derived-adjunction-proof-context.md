# SheafOfModules.SequenceProjection.derivedAdjunction

## Reason

The stage-3 static interface check classifies newly added module-level `variable`
commands as changes to what importers see. This delivery adds a proof context for
private constructions and two private instances on the private functors. This
record documents those commands; every existing public signature, definition body
and public import is unchanged. No target statement or its meaning changes.

## Old

The existing module-variable context is:

```lean
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
```

There is no `A`, `B`, `α` module-variable command and no private extension or direct-image
instance in the original file. Its existing options are:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

## New

The existing module-variable context and options remain. The new private proof
context is:

```lean
variable (A : Sheaf J CommRingCat.{w}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
  (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
```

The unused-section-variable linter is disabled because some proved private helpers
need only a subset of the surrounding assumptions:

```lean
set_option linter.unusedSectionVars false
```

The following private instances are fully proved, and apply only to the private
functors constructed in this file:

```lean
private instance extension_additive : (extension A B α).Additive where
  map_add {M N} f g := by
    apply system_ext B
    intro n
    change (scalar A B α n).model.E.map (f + g) = _
    rw [(scalar A B α n).model.E.map_add]
    exact ((systemEvaluation B n).map_add (f := (extension A B α).map f)
      (g := (extension A B α).map g)).symm

private instance directImage_additive : (directImage A B α).Additive :=
  (ordinaryAdjunction A B α).right_adjoint_additive
```

The public theorem still binds `A`, `B`, `α` explicitly, with exactly its original
signature. The new context provides arguments for private proof helpers; it adds
no assumption to any existing declaration. The linter option changes diagnostics
only. The two instances have private functors in their types and do not alter
any instance on an existing public functor or category.

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction
--uses SheafOfModules.SequenceProjection.derivedAdjunction` reports zero downstream
modules and one textual occurrence, the declaration in the item itself. No consumer
module requires adaptation. The item is still required by unfinished DAG parents;
no withdrawal or parent dependency change is proposed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction | V3 | Existing public signatures unchanged; private proof context and proved additive instances added; theorem hole closed. |

No target review is reopened: no public definition or statement has changed.

## Status

landed 20261021T120817-L-3950966 2026-10-21 (merge of deliver/V3/Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction)
