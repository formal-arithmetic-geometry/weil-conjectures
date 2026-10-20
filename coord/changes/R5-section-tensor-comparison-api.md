# CategoryTheory.InternalAbelianSheafModule.exists_sectionTensorIso

## Reason

The tensor isomorphism needed by InternalSectionTensorComparison already has a complete
private construction in the unclaimed module InternalSectionModuleFlat. Expose its existence
and its canonical pairing equation instead of duplicating that construction. This is an API
addition; no existing signature, definition, instance, visibility or public import changes.

## Old

The module has no public declaration of the tensor isomorphism. Its existing public theorem
remains verbatim:

```lean
theorem flat_iff_sectionModule (M : IM) :
    ObjectProperty.flat M ↔ SheafOfModules.IsFlatOnSite ((E).obj M)
```

## New

The following proved theorem is added (the local notation E is sectionModuleFunctor J R,
and IM is Mod (Sheaf J AddCommGrpCat) R):

```lean
theorem exists_sectionTensorIso (M N : IM) :
    ∃ e : (E).obj (M ⊗ N) ≅ (PresheafOfModules.sheafification
        (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (sectionRingSheaf J R)) (𝟙 _)).obj
        (((E).obj M).val ⊗ ((E).obj N).val),
    ∀ (U : Cᵒᵖ) (x : M.X.obj.obj U) (y : N.X.obj.obj U),
      (e.hom.val.app U)
          (((Mod.tensorObjπ M N).hom.app U)
            (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) M.X N.X).app U)
              (x ⊗ₜ[ℤ] y))) =
        ((toSheafify J ((((E).obj M).val ⊗ ((E).obj N).val).presheaf)).app U)
          (x ⊗ₜ[(sectionRingSheaf J R).obj.obj U] y)
```

## Users

The downstream.py audit found 227 transitive importers and the following three textual
users of flat_iff_sectionModule. Every existing user keeps exactly its original interface;
the new theorem is used only by the item module. No consumer adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.InternalSectionModuleFlat | unclaimed | Added proved public API; existing flatness theorem unchanged. |
| Sheaf.Paper.ConstantToContinuousScalarFlat | unclaimed in shared claim records | Existing flatness use unchanged. |
| Sheaf.Paper.InverseImageModuleFlat | unclaimed in shared claim records | Both existing flatness uses unchanged. |
| Sheaf.CategoryTheory.InternalSectionTensorComparison | R5 | Uses the added theorem to construct the normalized tensor comparison. |

No target statement or definition used by a target changes.

## Status

landed 20261020T221335-L-4176028 2026-10-20 (merge of deliver/R5/Sheaf.CategoryTheory.InternalSectionTensorComparison)
