# AlgebraicGeometry.ProEtale.CondensedRing.detSfCompactSupport

## Reason

The refinement calculation needs to compare the compact-support object with the literal
open-extension/direct-image composite underneath the total derived pullback. With the
ordinary definition, elaboration takes seconds but kernel conversion reaches its
deterministic timeout (roughly 90 seconds in profiling). Normalize this alias eagerly by
making it an abbreviation. Its type, parameters, universes, docstring and complete body
stay identical; it remains the actual derived compact-support composite. This changes
reduction behavior and no mathematical object or target statement.

The defining module was unclaimed on the server when the repair began. The earlier
interface change used an ordinary definition to limit eager reduction; this repair must
therefore also check that its existing consumers still compile without adaptations.

## Old

```lean
noncomputable def detSfCompactSupport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {A B : Scheme.{u}} {h : A ⟶ B}
    (d : Compactification h) :
    DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1}) (condensedRingObj Λ A)) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B)) :=
  rightDerivedLowerShriekOfCompactification Λ d
```

## New

```lean
noncomputable abbrev detSfCompactSupport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {A B : Scheme.{u}} {h : A ⟶ B}
    (d : Compactification h) :
    DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1}) (condensedRingObj Λ A)) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B)) :=
  rightDerivedLowerShriekOfCompactification Λ d
```

## Users

The direct-import search lists the item, IntegralCompactSupportDefs and
DetSfCompCompositionBaseChange. Textual use of the changed name outside its defining
module occurs only in DetSfCompCompositionBaseChange. The two new modules are also
compiled against the change. All direct importers compiled against the change within 60 seconds per file. The
temporary unchanged consumer copies were removed from the packet after validation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.DetSfCompBaseChangeDefs | unclaimed | Alias reduction behavior changes. |
| Sheaf.SixFunctors.CompactSupportRefinementBaseChange | K1 | Uses normalized object indices in its proof. |
| Sheaf.SixFunctors.IntegralCompactSupportDefs | unclaimed | Validation against the change; no source adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Validation against the change; no source adaptation. |
| Sheaf.SixFunctors.CompactSupportProperTriangle | new in this packet | States the proper-pasting step. |
| Sheaf.SixFunctors.CompactSupportOpenRefinementPasting | new in this packet | States the local step. |

## Status

landed 20261027T210118-L-1658029 2026-10-27 (merge of deliver/K1/Sheaf.SixFunctors.CompactSupportRefinementBaseChange)
