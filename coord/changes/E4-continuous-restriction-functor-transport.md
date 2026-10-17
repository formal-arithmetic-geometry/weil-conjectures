# AlgebraicGeometry.ProEtale.CondensedRing.continuousField_module_restriction

## Reason

Repair the upstream-sync return against the current library. The retained direct application
of `continuousRing_module_restriction` timed out in kernel checking: its pullback uses the
`CommRing.toRing` projection, whereas the field theorem uses `DivisionRing.toRing`.
These ring structures are definitionally equal, but comparing their scalar-extension objects
unfolded the tensor and sheafification constructions. First compare the pullback functors by
`rfl`, then apply the induced isomorphism to the module and map it through the encoding.
The proof now uses that explicit isomorphism before transporting the coefficient sheaves.

The upstream `InternalHom` module now imports successfully and supplies the monoidal
localization comparison. Its existing instance replaces the old private specialization.
All existing public signatures, visibility, definitions, and target meanings are unchanged.
No local or global instance is introduced.

## Old

The repository field theorem has its original signature and proof `:= by sorry`.
The retained returned proof ended with the following direct specialization:

```lean
  obtain ⟨e⟩ := continuousRing_module_restriction X Y f E P
  exact field_restriction_transport ℓ E X Y f P _ e
```

## New

The same theorem signature now has a complete proof. After constructing the totally
separated topology, its final steps are (the existing instance binder is named `hE` by `rename_i`):

```lean
  have hF :
      upperStar (@Profinite.continuousMapRingObj E _ hE.toField.toDivisionRing.toRing _) f =
        upperStar (@Profinite.continuousMapRingObj E _ hE.toField.toCommRing.toRing _) f := rfl
  obtain ⟨e⟩ := continuousRing_module_restriction X Y f E P
  let eU := (eqToIso hF).app P
  let e' := (SheafOfModules.forget _).mapIso
    ((continuousRingModuleEquivalence Y E).functor.mapIso eU) ≪≫ e
  exact field_restriction_transport ℓ E X Y f P _ e'
```

`field_restriction_transport` and the presheaf pushforward square are proved private helpers.
The unused retained raw-pullback definition and comparison are removed.

## Users

`tools/downstream.py --uses continuousField_module_restriction` names the item and the lattice
module. The slice-freeness module is the other direct importer. No consumer is adapted.
The 24 transitive downstream modules keep the same interface and mathematical statements.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | E4 | Complete field restriction proof with explicit functor transport. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | Existing theorem application is unchanged. |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | F1 | Existing import and ring-restriction application are unchanged. |

## Status

landed 20261017T013734-L-113407 2026-10-17 (merge of deliver/E4/Sheaf.Paper.ContinuousModuleEncodingRestriction)
