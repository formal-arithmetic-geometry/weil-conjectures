# SheafOfModules.exists_changeOfRings_tensorCancellation_sections

## Reason

The derived restriction formula requires the sectionwise balanced formula for the same
natural cancellation isomorphism. The existing theorem exposes naturality, while its
constructed isomorphism and its generator computation were private. Expose that computation
as an additional proved theorem. Its witness is the original constructed isomorphism;
no data is chosen from an unproved existence statement.

The existing public theorem retains its signature and all public imports verbatim.
Its naturality proof is factored into a private proved helper and reused by both theorems.
The module has no current claim in this repository snapshot.

## Old

```lean
theorem exists_changeOfRings_tensorCancellation_independentCoefficients (α : R ⟶ S) :
    ∃ e : ∀ (M : SheafOfModules.{r} (𝓡 S))
        (N : SheafOfModules.{r} (𝓡 R)),
      (restrictScalars (𝓻 α)).obj
        ((monoidalCategory S).tensorObj M (changeOfRings α N)) ≅
      (monoidalCategory R).tensorObj ((restrictScalars (𝓻 α)).obj M) N,
      ∀ {M M' : SheafOfModules.{r} (𝓡 S)}
        {N N' : SheafOfModules.{r} (𝓡 R)} (f : M ⟶ M') (g : N ⟶ N'),
        (restrictScalars (𝓻 α)).map
            ((monoidalCategory S).tensorHom f (changeOfRingsHom α N g)) ≫
          (e M' N').hom =
        (e M N).hom ≫
          (monoidalCategory R).tensorHom ((restrictScalars (𝓻 α)).map f) g := by
  -- existing proved body
```

## New

The old theorem is preserved. The following proved normalization API is added:

```lean
theorem exists_changeOfRings_tensorCancellation_sections (α : R ⟶ S) :
    ∃ e : ∀ (M : SheafOfModules.{r} (𝓡 S)) (N : SheafOfModules.{r} (𝓡 R)),
      (restrictScalars (𝓻 α)).obj
        ((monoidalCategory S).tensorObj M (changeOfRings α N)) ≅
      (monoidalCategory R).tensorObj ((restrictScalars (𝓻 α)).obj M) N,
      (∀ {M M' : SheafOfModules.{r} (𝓡 S)} {N N' : SheafOfModules.{r} (𝓡 R)}
        (f : M ⟶ M') (g : N ⟶ N'),
        (restrictScalars (𝓻 α)).map
            ((monoidalCategory S).tensorHom f (changeOfRingsHom α N g)) ≫
          (e M' N').hom =
        (e M N).hom ≫
          (monoidalCategory R).tensorHom ((restrictScalars (𝓻 α)).map f) g) ∧
      (∀ (M : SheafOfModules.{r} (𝓡 S)) (N : SheafOfModules.{r} (𝓡 R))
        (W : Cᵒᵖ) (m : M.val.obj W) (s : S.obj.obj W) (n : N.val.obj W),
        (e M N).hom.val.app W
          ((tensorObjIsoSheafification M (changeOfRings α N)).inv.val.app W
            (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)).unit.app
              (M.val ⊗ (changeOfRings α N).val)).app W
                (m ⊗ₜ[S.obj.obj W]
                  ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)).unit.app
                    (changeOfRingsPresheaf α N)).app W
                      (s ⊗ₜ[R.obj.obj W,(α.hom.app W).hom] n)))) =
        (tensorObjIsoSheafification ((restrictScalars (𝓻 α)).obj M) N).inv.val.app W
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R).obj)).unit.app
            (((restrictScalars (𝓻 α)).obj M).val ⊗ N.val)).app W
              ((s • m) ⊗ₜ[R.obj.obj W] n))) := by
  -- proved from the original constructed isomorphism
```

## Users

Refreshed from the current shared sources on 2026-10-21. All existing declaration
users below retain their signatures; no consumer adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients | unclaimed | Original API unchanged; no adaptation. |
| Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients | unclaimed | Original API unchanged; no adaptation. |
| Sheaf.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients | unclaimed | Adds proved section and naturality APIs; preserves the original theorem. |
| Sheaf.Algebra.Homology.FlatCoefficientReductionAdjunct | unclaimed | Original API unchanged; no adaptation. |
| Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat | unclaimed | Original API unchanged; no adaptation. |
| Sheaf.Paper.FlatCommonQuotientReductionTower | unclaimed | Original API unchanged; no adaptation. |
| Sheaf.Paper.SiteDerivedTensorRestriction | D3 | Uses the additional proved APIs. |

## Status

landed 20261021T233637-L-842487 2026-10-21 (merge of deliver/D3/Sheaf.Paper.SiteDerivedTensorRestriction)

## Reusing the existing tensor naturality proof

The public wrapper below exposes the module's already proved private naturality lemma.
The restriction module uses it instead of duplicating its proof. It has no added hole,
and the original private declaration and all existing public signatures are retained.

```lean
/-- Naturality of the tensor/sheafification comparison at independent site universes.
This exposes the comparison used in the constructed cancellation map.
Source: Stacks, Tag 03EK
(blueprint: lem-pur-change-of-rings-tensor-cancellation-independent). -/
theorem changeOfRingsTensorIso_naturality_independentCoefficients
    (A : Sheaf J CommRingCat.{r})
    {M M' N N' : SheafOfModules.{r} (𝓡 A)} (f : M ⟶ M') (g : N ⟶ N') :
    letI := monoidalCategory A
    (f ⊗ₘ g) ≫ (tensorObjIsoSheafification M' N').hom =
      (tensorObjIsoSheafification M N).hom ≫
        (PresheafOfModules.sheafification (𝟙 (𝓡 A).obj)).map (f.val ⊗ₘ g.val) :=
  cancellationTensorIso_naturality A f g


```
