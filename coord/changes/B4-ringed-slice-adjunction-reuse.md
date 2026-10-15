# CategoryTheory.extensionSheafAdjunction_nonempty

## Reason

The returned delivery duplicated three private theorems from
`Sheaf.Algebra.Homology.LocalizedRestrictionExtensionExists`. Its full concrete
adjunction construction is already proved, but private. Expose a propositional
interface for that construction in place, and reuse it in the item. This module
is unclaimed (no claim lock at repair time). No existing declaration changes
signature or visibility; the private construction and its helpers remain private.

## Old

No public `CategoryTheory.extensionSheafAdjunction_nonempty` declaration.
`Sheaf.CategoryTheory.ExtensionByZeroPresheaf` was imported privately, and so was
`Mathlib.Algebra.Category.Grp.FilteredColimits`; there were no direct public imports
of module sheafification.

## New

```lean
theorem extensionSheafAdjunction_nonempty
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C) :
    Nonempty ((SheafOfModules.extensionByZeroPresheaf.{max u v} R U ⋙
      PresheafOfModules.sheafification.{max u v} (𝟙 R.obj)) ⊣
        SheafOfModules.overFunctor.{max u v} R U) :=
  ⟨extensionSheafAdjunction R U⟩
```

Publicly import `Sheaf.CategoryTheory.ExtensionByZeroPresheaf` and
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` because the new public
signature mentions their definitions. Also publicly import
`Mathlib.Algebra.Category.Grp.FilteredColimits` for the instances required to
elaborate sheafification for arbitrary topologies in this public signature. Add this public helper to the existing
node's `lean.declarations`; it exposes step 1 of the already proved argument,
not a new mathematical obligation. Its proof uses no choice and no sorry.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.LocalizedRestrictionExtensionExists | unclaimed | Add the proved public interface and the public imports; all existing declarations remain unchanged. |
| Sheaf.CategoryTheory.RingedSliceExtensionPreservesExact | B4 | Replace the duplicate construction by the new public interface. |

`tools/downstream.py --uses extensionSheafAdjunction` finds only the defining
module using the old private name. None of the other downstream modules can use
that private construction. The existing existential theorem remains unchanged,
so no downstream adaptation is needed and no target's meaning changes.

## Status

landed 20261015T232823-L-3301124 2026-10-15 (merge of deliver/B4/Sheaf.CategoryTheory.RingedSliceExtensionPreservesExact)
