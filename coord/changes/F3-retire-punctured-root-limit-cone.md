# AlgebraicGeometry.Scheme.pointed_etale_ring_colimit

## Reason

Retire the duplicate Sheaf module under the human's instruction in
coord/changes/retire-sheaf-twins-20261020.md and its row in coord/retire-items.tsv.
The module has zero holes. Its official twin proves the ring-colimit theorem for
strictHenselization, whereas the Sheaf copy used strictHenselizationRing. These
are canonically isomorphic colimits of the same representative diagram; replacing
one by the other requires checking the structural maps, rather than renaming a binder.

## Old

The withdrawn Sheaf module declares:

```lean
theorem pointed_etale_ring_colimit
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (y : Spec R) (hy : ∀ x : Spec (.of Ω), barY x = y)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    ∃ (I : Type u) (cat : Category.{u} I), letI := cat
      ∃ (_ : IsCofiltered I) (F : Iᵒᵖ ⥤ CommRingCat.{u}) (c : Cocone F)
        (a : (Functor.const Iᵒᵖ).obj R ⟶ F)
        (e : c.pt ≅ strictHenselizationRing barY),
        Nonempty (IsColimit c) ∧
        (∀ j, a.app j ≫ c.ι.app j ≫ e.hom = b) ∧
        ∀ j, Etale (Spec.map (a.app j)) ∧
          ∃ z : Spec (F.obj j), (Spec.map (a.app j)) z = y
```

The only direct importer, PuncturedRootLimitPresentation, privately imports this copy
and publicly imports Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap.

## New

Use the unchanged adopted source declaration:

```lean
theorem pointed_etale_ring_colimit
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (y : Spec R) (hy : ∀ x : Spec (.of Ω), barY x = y)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY) :
    ∃ (I : Type u) (cat : Category.{u} I), letI := cat
      ∃ (_ : IsCofiltered I) (F : Iᵒᵖ ⥤ CommRingCat.{u}) (c : Cocone F)
        (a : (Functor.const Iᵒᵖ).obj R ⟶ F)
        (e : c.pt ≅ strictHenselization barY),
        Nonempty (IsColimit c) ∧
        (∀ j, a.app j ≫ c.ι.app j ≫ e.hom = b) ∧
        ∀ j, Etale (Spec.map (a.app j)) ∧
          ∃ z : Spec (F.obj j), (Spec.map (a.app j)) z = y
```

Withdraw only lean/Sheaf/AlgebraicGeometry/Morphisms/PuncturedRootLimitCone.lean
via deleted.txt and move its DAG attachment to the official twin.

The consumer imports the twin privately and imports the two existing upstream
statement dependencies directly. Its theorem signature is byte-for-byte unchanged.
A fully proved private theorem strictHenselization_colimit_comparison gives

```lean
    ∃ e : strictHenselizationRing barY ≅ strictHenselization barY,
      Spec.map e.hom ≫ strictHenselizationStructuralMap barY =
        strictLocalizationToBase barY
```

The isomorphism is the unique isomorphism between the canonical colimit cocone
and smallStrictHenselizationCocone. Its coprojection equation, followed by the two
structural-map leg equations, proves the displayed equality. Apply the official
theorem to b followed by e.hom; compose its comparison isomorphism with e.symm
and cancel e.hom followed by e.inv in the cocone equations. The original
punctured_root_colimit_continuity application then applies unchanged.

The Sheaf structural-map wrapper must leave this consumer's imports because it
exports the old strictHenselizationStructuralMap_eq, which shares its name with
the official extension's equation for the new ring model. Its actual statement
dependencies, StrictHenselizationExtension and StrictHenselizationStructuralMap,
are imported directly, preserving the consumer's original statement objects.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootLimitCone | F3 | Withdraw duplicate; node points at the proved official twin. |
| Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootLimitPresentation | unclaimed | Replace imports; add the private comparison proof and transport the cocone; public theorem signature unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootSectionEtaleDescent | unclaimed | Transitive consumer; no edits, compiled against the adapted presentation. |

The direct importer search over lean/ and quarantine/ finds only the presentation.
The downstream search finds these two consumers. The source-library consumer
WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedRootLimitPresentation already
uses the official twin and requires no change. No upstream file, target statement,
or definition changes. The unit's ring-colimit and root-continuity route remains.

## Status

landed 20261020T162912-L-3674008 2026-10-20 (merge of deliver/F3/Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootLimitCone)
