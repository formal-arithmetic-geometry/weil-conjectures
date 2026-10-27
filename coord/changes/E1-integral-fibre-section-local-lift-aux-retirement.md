# AlgebraicGeometry.Etale.exists_integralStrictLocalFibreComparison

## Reason

Complete the assigned zero-hole retirement in coord/retire-items.tsv. The Sheaf copy
uses the small affine-diagram colimit, while its adopted twin uses the full affine
pointed-neighbourhood colimit. They are canonically isomorphic, not definitionally equal.
The listed consumer has already been retired: its current adopted realization imports
and applies the full-model twin. Thus no consumer needs the obsolete small-model theorem.
The mathematical parent dependency stays, attached to the adopted theorem.

The canonical comparison is smallStrictHenselizationColimitIso; the theorem
smallStrictHenselizationColimitIso_toBase identifies its Spec map followed by
strictLocalizationToBase with strictHenselizationStructuralMap. The two qcqs restriction
formulas are the inverse-image units along the corresponding limit legs. The existing
adopted consumer combines full-model continuity and fibre comparison directly, so no
transport lemma or replacement duplicate is needed.

## Old

The withdrawn Sheaf declaration had this signature:

```lean
theorem exists_integralStrictLocalFibreComparison
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s) [IsIntegralHom f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ e : (Sheaf.Γ (pullback f (strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (strictHenselizationStructuralMap s))).obj F) ≅
      ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 X'))),
      ∀ j : SmallModel.{u} (strictHenselizationNeighbourhoods s),
        unitSectionRestriction Λ
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) F
          (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
            ((equivSmallModel.{u}
              (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))
          ((pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
            Scheme.smallStrictHenselizationBaseChangeMap f s j)
          (by
            change _ ≫ pullback.snd _ f =
              pullback.fst f (Scheme.strictHenselizationStructuralMap s)
            simp only [Category.assoc, Scheme.smallStrictHenselizationBaseChangeMap_snd,
              pullbackSymmetry_hom_comp_snd]) ≫ e.hom =
          geometricFibreSectionRestriction Λ sq.toCommSq F
            ((AffineEtale.Spec Y).obj
              ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)
            ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2
```

## New

The node attaches to the existing adopted theorem, with exact signature:

```lean
theorem exists_integralStrictLocalFibreComparison
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s) [IsIntegralHom f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ e : (Sheaf.Γ (pullback f (strictLocalizationToBase s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (strictLocalizationToBase s))).obj F) ≅
      ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 X'))),
      ∀ j : SmallModel.{u} (strictHenselizationNeighbourhoods s),
        qcqsStrictLocalSectionRestriction Λ f s F j ≫ e.hom =
          geometricFibreSectionRestriction Λ sq.toCommSq F
            ((AffineEtale.Spec Y).obj
              ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)
            ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2
```

The adopted theorem and its proof are unchanged. The Sheaf module is withdrawn via
deleted.txt; no replacement declaration, axiom or sorry is introduced. The node statement
and proof record the adopted presentation and proof, with a statement_change auditing the
sole mathematical citer. No DAG node is deleted. The small-model compatibility APIs used
elsewhere are left alone.

## Users

The current tools/downstream.py census reports zero modules downstream of the Sheaf
copy. Searches of lean/Sheaf, lean/WeilConjectures and quarantine find no remaining import
of the copy. The retire-items row names the old Sheaf consumer; the current DAG realization
of that consumer is already the adopted module below. It privately imports the adopted
comparison, and lines 61 onward obtain both full-model isomorphisms and combine their
representative formulas. This is the actual replacement argument, not an inference from
zero Lean importers alone.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLift | retired; absent | Historical listed consumer, replaced by its adopted realization. |
| WeilConjectures.AlgebraicGeometry.IntegralFibreSectionLocalLift | not edited | Already imports the adopted twin; exact source and theorem signature retained; compile checked. |
| WeilConjectures.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux | not edited | Existing replacement theorem; exact source, public imports and proof retained; compile checked. |

The sole current DAG citer is lem-sbc-integral-fibre-section-local-lift and remains valid.
The unit sk-lem-universal-datum has empty realized statement and step lists, so no unit
statement or proof step is removed or bypassed. There is no target statement change, and no
definition used by a target changes. No upstream file is delivered or altered.

## Status

landed 20261022T032523-L-2035275 2026-10-22 (merge of deliver/E1/Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux)
