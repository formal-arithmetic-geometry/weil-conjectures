# Sheaf.Topology.SpectralSpaceCohomologyDimension proof commands

## Reason

The item held by T6 is proved using private helpers and local transparency controls.
The static interface checker conservatively flags module-level command changes.
This record documents their scope: no existing public signature, public import,
instance registration, notation or mathematical definition is changed.

## Old

The original checking context was:

```lean
set_option autoImplicit false
universe u
open CategoryTheory TopologicalSpace
namespace TopCat.Sheaf
```

The public theorem signature was:

```lean
theorem subsingleton_H'_top_of_spectralSpace_of_dimension_le
    (T : Type u) [TopologicalSpace T] [SpectralSpace T]
    (d : ℕ) (hd : topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (q : ℕ) (hq : d < q) :
    Subsingleton
      (@CategoryTheory.Sheaf.H'.{u, u, u}
        (Opens T) inferInstance (Opens.grothendieckTopology T) inferInstance
        (@hasExt_of_enoughInjectives _ _ _ inferInstance
          (@IsGrothendieckAbelian.enoughInjectives _ _ _
            (CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
              (Opens.grothendieckTopology T) AddCommGrpCat.{u}))) F q ⊤)
```

## New

The checking context now includes:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology
namespace TopCat.Sheaf
```

The extra universe belongs to a private generic dimension-shifting helper.
Namespace openings and elaborator options affect checking this file only.
Explicitly local irreducible/semireducible attributes for
`CategoryTheory.Sheaf.cohomologyPresheafFunctor` keep functorial arguments abstract
and restore unfolding for direct Ext calculations. The `locally_zero` helper
scopes `backward.isDefEq.respectTransparency false` to its own declaration.
No attribute is registered globally. Every new helper and the constructed
Mayer--Vietoris square is private and has a complete body.

The public signature is unchanged, with only a line break in its binders:

```lean
theorem subsingleton_H'_top_of_spectralSpace_of_dimension_le
    (T : Type u) [TopologicalSpace T]
    [SpectralSpace T]
    (d : ℕ) (hd : topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (q : ℕ) (hq : d < q) :
    Subsingleton
      (@CategoryTheory.Sheaf.H'.{u, u, u}
        (Opens T) inferInstance (Opens.grothendieckTopology T) inferInstance
        (@hasExt_of_enoughInjectives _ _ _ inferInstance
          (@IsGrothendieckAbelian.enoughInjectives _ _ _
            (CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
              (Opens.grothendieckTopology T) AddCommGrpCat.{u}))) F q ⊤)
```

## Users

`tools/downstream.py` with this module and `--uses` for its public theorem reports
zero current Lean importers and one textual use, the item itself. DAG parents still
need the theorem; its attachment and public signature are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Topology.SpectralSpaceCohomologyDimension | T6 | Private proof helpers and local checking commands; public signature unchanged. |

No other module is adapted. The complete module compiled in 42.9 seconds, and the
subsequent delivery compile and axiom probe passed before requesting this record.

## Status

landed 20261024T020601-L-2622073 2026-10-24 (merge of deliver/T6/Sheaf.Topology.SpectralSpaceCohomologyDimension)
