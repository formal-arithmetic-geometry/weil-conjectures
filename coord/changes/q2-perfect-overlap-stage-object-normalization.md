# AlgebraicGeometry.perfectOverlapStageObjectIso

## Reason

Restore the quarantined adapter using the unchanged canonical source construction. The
source associates its composition comparisons through the cartesian map first; the archive
associated them through the open inclusion first. Their public types agree. The restored
`perfectOverlapStageObjectIso_hom_app` proves the archived component formula for the source
construction from the pinned composition associativity theorem. No source file or target
statement changes. The inclusion comparison used by both constructions is covered by
`q2-perfect-overlap-stage-canonical-adapter.md`.

## Old

The archived definition, verbatim:

```lean
noncomputable def perfectOverlapStageObjectIso
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (p' : X ⟶ T) (p : Y ⟶ S) (q : T ⟶ S)
    (h : IsPullback g p' p q) (U V L : Y.Opens) (hWL : U ⊓ V ≤ L) :
    (derivedPullback (g ∣_ L) ⋙
      (schemeOpenOverlapRestriction X (homOfLE
        (show g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ L from fun _ hx ↦ hWL hx))).mapDerivedCategory) ⋙
      (perfectOverlapStageEquivalence g p' p q h U V).functor ≅
    derivedPullback (Y.homOfLE hWL) ⋙
      derivedPullback (pullback.fst ((U ⊓ V).ι ≫ p) q) := by
  let hW' : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ L := fun _ hx ↦ hWL hx
  let square := (isPullback_morphismRestrict g (U ⊓ V)).paste_vert h
  let e := square.isoPullback
  have restricted : X.homOfLE hW' ≫ (g ∣_ L) =
      (g ∣_ (U ⊓ V)) ≫ Y.homOfLE hWL := by
    apply (cancel_mono L.ι).1
    simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
    rw [← Category.assoc, Scheme.homOfLE_ι]
    rfl
  have fac : e.inv ≫ (X.homOfLE hW' ≫ (g ∣_ L)) =
      pullback.fst ((U ⊓ V).ι ≫ p) q ≫ Y.homOfLE hWL := by
    calc
      e.inv ≫ (X.homOfLE hW' ≫ (g ∣_ L)) =
          e.inv ≫ ((g ∣_ (U ⊓ V)) ≫ Y.homOfLE hWL) := by rw [restricted]
      _ = (e.inv ≫ (g ∣_ (U ⊓ V))) ≫ Y.homOfLE hWL := by
            simp only [Category.assoc]
      _ = _ := by rw [square.isoPullback_inv_fst]
  change (derivedPullback (g ∣_ L) ⋙
    (schemeOpenOverlapRestriction X (homOfLE hW')).mapDerivedCategory) ⋙
    derivedPullback e.inv ≅ _
  exact Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft _
        (overlapOpenInclusionPullbackIso X (homOfLE hW')).symm ≪≫
          perfectHomComposition (X.homOfLE hW') (g ∣_ L)) _ ≪≫
    perfectHomComposition e.inv (X.homOfLE hW' ≫ (g ∣_ L)) ≪≫
    eqToIso (congrArg (fun f ↦ derivedPullback f) fac) ≪≫
    (perfectHomComposition (pullback.fst ((U ⊓ V).ι ≫ p) q) (Y.homOfLE hWL)).symm
```

## New

The unchanged adopted-source definition supplied by the adapter's public import, verbatim:

```lean
noncomputable def perfectOverlapStageObjectIso
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (p' : X ⟶ T) (p : Y ⟶ S) (q : T ⟶ S)
    (h : IsPullback g p' p q) (U V L : Y.Opens) (hWL : U ⊓ V ≤ L) :
    (derivedPullback (g ∣_ L) ⋙
      (schemeOpenOverlapRestriction X (homOfLE
        (show g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ L from fun _ hx ↦ hWL hx))).mapDerivedCategory) ⋙
      (perfectOverlapStageEquivalence g p' p q h U V).functor ≅
    derivedPullback (Y.homOfLE hWL) ⋙
      derivedPullback (pullback.fst ((U ⊓ V).ι ≫ p) q) := by
  let hW' : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ L := fun _ hx ↦ hWL hx
  let square := (isPullback_morphismRestrict g (U ⊓ V)).paste_vert h
  let e := square.isoPullback
  have restricted : X.homOfLE hW' ≫ (g ∣_ L) =
      (g ∣_ (U ⊓ V)) ≫ Y.homOfLE hWL := by
    apply (cancel_mono L.ι).1
    simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
    rw [← Category.assoc, Scheme.homOfLE_ι]
    rfl
  have fac : (e.inv ≫ X.homOfLE hW') ≫ (g ∣_ L) =
      pullback.fst ((U ⊓ V).ι ≫ p) q ≫ Y.homOfLE hWL := by
    rw [Category.assoc, restricted, ← Category.assoc]
    rw [square.isoPullback_inv_fst]
  change (derivedPullback (g ∣_ L) ⋙
    (schemeOpenOverlapRestriction X (homOfLE hW')).mapDerivedCategory) ⋙
    derivedPullback e.inv ≅ _
  exact Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft _ (overlapOpenInclusionPullbackIso X (homOfLE hW')).symm) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (perfectHomComposition e.inv (X.homOfLE hW')) ≪≫
    perfectHomComposition (e.inv ≫ X.homOfLE hW') (g ∣_ L) ≪≫
    eqToIso (congrArg (fun f ↦ derivedPullback f) fac) ≪≫
    (perfectHomComposition (pullback.fst ((U ⊓ V).ι ≫ p) q) (Y.homOfLE hWL)).symm
```

## Users

The current `tools/downstream.py --allow-missing --uses` query has no active Lean users:
the item and its consumers are quarantined. This is not treated as withdrawal authority.
The direct quarantined importers and the indirect user of the restored helper were read;
none unfolds the old descent construction. Their node attachments and dependency links
remain intact. All use the same exported types and helper equations.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.PerfectOverlapCompositeSiteComponent` | unclaimed | Constructed source names and archived helper signatures preserved; no edit. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackNormalization` | unclaimed | Uses the restored hom-component equation through the nested-square interface; signature preserved. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare` | unclaimed | Constructed source names and archived helper signatures preserved; no edit. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreBase` | unclaimed | Constructed source names and archived helper signatures preserved; no edit. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreCanonicalFamily` | unclaimed | Constructed source names and archived helper signatures preserved; no edit. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons` | unclaimed | Constructed source names and archived helper signatures preserved; no edit. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreData` | unclaimed | Constructed source names and archived helper signatures preserved; no edit. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreOfData` | unclaimed | Constructed source names and archived helper signatures preserved; no edit. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport` | unclaimed | Constructed source names and archived helper signatures preserved; no edit. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositionComponent` | unclaimed | Constructed source names and archived helper signatures preserved; no edit. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionComponent` | unclaimed | Uses the restored stage-object component equation; signature preserved. |

No consumer is adapted. No source-library declaration, signature, attribute, public import,
or data body is changed. Targets that use these definitions retain the adopted source
construction; the restored adapter and its compatibility proof are available for semantic
review together with this change record.

## Status

landed 20261020T230822-L-616945 2026-10-20 (merge of deliver/Q2/Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence)
