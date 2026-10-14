# SheafOfModules.fieldScalarPresheafPullback_isRightAdjoint

## Reason

The static preflight treats new `variable` and `section` commands as a potential
interface change. They scope private helpers only. The scalar-extension construction
and all its supporting lemmas are private; the added elaboration option is confined
to the closed PresheafExtension section. No existing definition, statement, visibility,
public import, instance registration, or attribute is changed. This record lets the
independent reader verify that fact. The target statements retain their meaning.

## Old

```lean
theorem fieldScalarPresheafPullback_isRightAdjoint
    {k : Type u} [Ring k] (X : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (α : k →+* R.obj.obj (op ⊤)) :
    (PresheafOfModules.pushforward.{max u v}
      (fieldScalarPresheafRingMap X R α)).IsRightAdjoint := by sorry
```

## New

```lean
theorem fieldScalarPresheafPullback_isRightAdjoint
    {k : Type u} [Ring k] (X : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (α : k →+* R.obj.obj (op ⊤)) :
    (PresheafOfModules.pushforward.{max u v}
      (fieldScalarPresheafRingMap X R α)).IsRightAdjoint := by
  exact (Adjunction.adjunctionOfEquivLeft
    (fun V N ↦ extensionHomEquiv X R α V N)
    (fun V N N' g f ↦ by
      ext U m
      rfl)).isRightAdjoint
```

The construction is in two new sections, ScalarExtension and PresheafExtension,
closed before the existing public theorem. Their section variables are binders of
private declarations, not new assumptions of the existing public theorem.

## Users

`tools/downstream.py` reports 277 transitive importing modules. Its `--uses
SheafOfModules.fieldScalarPresheafPullback_isRightAdjoint` scan finds the five
modules below. Every downstream statement and definition sees the identical
public signature and public imports; the new construction remains private.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FieldScalarExtension | unclaimed | Same signature and public imports; proof now closed. No adaptation. |
| Sheaf.AlgebraicGeometry.FieldScalarExtensionAdjunction | unclaimed | Same signature and public imports; proof now closed. No adaptation. |
| Sheaf.AlgebraicGeometry.FieldScalarExtensionMono | unclaimed | Same signature and public imports; proof now closed. No adaptation. |
| Sheaf.AlgebraicGeometry.FieldScalarPresheafPullbackExists | M3 | Same signature and public imports; proof now closed. No adaptation. |
| Sheaf.AlgebraicGeometry.FieldScalarPresheafPullbackMono | A4 | Same signature and public imports; proof now closed. No adaptation. |

No module is adapted. These are proof-local implementation additions, not a
change of the objects or hypotheses used by any importer.

## Status

landed 20261014T033107-L-604106 2026-10-14 (merge of deliver/M3/Sheaf.AlgebraicGeometry.FieldScalarPresheafPullbackExists)
