# SheafOfModules.internalHomCoproductFanIsLimit

## Reason

The static interface check flags new namespace/variable commands as an interface change.
They scope entirely private helper constructions. All original public signatures, visibility,
imports and instance registrations are identical. No definition used by the target changes.
The commands merely supply binders to private presheaf helpers, close their namespace, and
reopen the original SheafOfModules namespace. Scoped transparency options end at each
private declaration. This record makes that conservative flag reviewable.

## Old

The module opened `namespace SheafOfModules` immediately after the existing universe/open
commands. Its only declaration had this signature:

```lean
theorem internalHomCoproductFanIsLimit {I : Type w} (M : I → Mod)
    (c : Cofan M) (hc : IsColimit c) (N : Mod) :
    Nonempty (IsLimit (Fan.mk (homObj (R := R) c.pt N)
      (fun i ↦ homObjMap (R := R) (c.inj i) (𝟙 N))))
```

## New

The displayed signature is identical. Before the original namespace block, the file adds:

```lean
namespace PresheafOfModules
variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v}}
  {A M N : PresheafOfModules.{max u v} (R ⋙ forget₂ _ _)}
```

All declarations in that block are private, then `end PresheafOfModules` closes the scope.
Three further private helpers live in the original SheafOfModules namespace. Each scoped
`set_option backward.isDefEq.respectTransparency false in` applies to a single private
helper only. The complete added constructions and proofs are in the delivered module.
No public signature, public data definition, attribute, notation or instance is changed.

## Users

`tools/downstream.py ... --uses internalHomCoproductFanIsLimit` found the following two
textual uses. The helper names are private and cannot be used by importers. The only direct
importer is HomTensorSummandRestriction, whose expected theorem signature remains identical;
no adaptation is required. The 419 transitive downstream modules inherit the same interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct | H2 | proof closed; signature identical |
| Sheaf.Algebra.Homology.HomTensorSummandRestriction | unclaimed | unchanged theorem use |

## Status

landed 20261013T100001-L-2461354 2026-10-13 (merge of deliver/H2/Sheaf.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct)
