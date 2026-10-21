# CategoryTheory.Mod.sheaf_finiteFreeScalarCoordinates

## Reason

Server stage-3 preflight flags the added `section Coordinates` and its `variable` commands
as potentially changing the module interface. This record documents their scope. They only
supply binders for private, fully proved helpers. `end Coordinates` closes that scope before
the existing public theorem. They introduce no instance, notation, attribute, or open namespace
for importers. The public predicate and theorem signatures, and all public imports, are
verbatim unchanged. There is no semantic statement or definition repair.

## Old

The existing public theorem has this signature:

```lean
theorem sheaf_finiteFreeScalarCoordinates
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) :
    @FiniteFreeScalarCoordinates (Sheaf J Ab.{w}) _
      (sfbSheafTensorStructure (A := Ab.{w}) J).monoidal
      (sfbSheafTensorStructure (A := Ab.{w}) J).symmetric.toBraidedCategory
      (@sheafIsAbelian C _ Ab.{w} _ _ J
        (hasSheafifyEssentiallySmallSite J Ab.{w}))
```

There was no `Coordinates` section or associated variable command.

## New

The public signature above is unchanged. Before its existing docstring the proof now has
this local helper section header, with all declarations in the section marked `private`:

```lean
section Coordinates

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [Abelian H] [MonoidalPreadditive H] [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R B : H} [MonObj R] [MonObj B] [IsCommMonObj R] [IsCommMonObj B]
  (φ : R ⟶ B) [IsMonHom φ]
```

The section also contains a local `variable {φ} {n : ℕ}` command for the coordinate helpers;
it is closed by `end Coordinates` before the public theorem. Thus none of these variable
commands changes the binders of a preexisting declaration. The helper definitions are actual
coequalizer and finite-biproduct isomorphism constructions, with every proof completed.
A private import of the existing module-object monoidal structure supplies these proofs.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FiniteFreeScalarCoordinates | K3 | One theorem proof completed; all existing public signatures and definitions unchanged. |

`python3 tools/downstream.py Sheaf.CategoryTheory.FiniteFreeScalarCoordinates --uses
FiniteFreeScalarCoordinates sheaf_finiteFreeScalarCoordinates` reports zero downstream
modules, and both names occur only in the item itself. A source search confirms there are
no current Lean importers. The unfinished DAG parent `lem-sfb-subfield-flat` still cites the
same node and receives its full original conclusion; it needs no adaptation. The target
statements and the definitions in their signatures have not changed.

## Status

landed 20261021T061441-L-1776006 2026-10-21 (merge of deliver/K3/Sheaf.CategoryTheory.FiniteFreeScalarCoordinates)
