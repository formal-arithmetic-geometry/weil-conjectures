# AlgebraicGeometry.Etale.strictLocalFibreRestriction and compatibility

## Reason

Complete the zero-hole retirement in coord/retire-items.tsv row 2901. The adopted
source library already provides these declarations using strictLocalization and
strictLocalizationToBase. The retired copy uses strictHenselizationScheme and
strictHenselizationStructuralMap, canonically isomorphic but not definitionally equal.
Import substitution would therefore fail to preserve the sole consumer's statement.

Withdraw the Sheaf duplicate. Preserve the adopted source module verbatim. In
Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux remove the private import
and construct the identical concrete section morphism as a proof-local let r.
Prove its representative restriction identity directly from unitSectionRestriction_comp,
the small-model leg projection formulas and pullback extensionality. No new public
or private declaration replaces the retired duplicate.

## Old

From lean/Sheaf/AlgebraicGeometry/StrictLocalFibreRestrictionCompatibility.lean:

```lean
noncomputable def strictLocalFibreRestriction
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {g' : X' ⟶ X} {f : X ⟶ Y}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {s : Spec (.of Ω) ⟶ Y}
    (i : X' ⟶ pullback f (strictHenselizationStructuralMap s))
    (hi : i ≫ pullback.fst f (strictHenselizationStructuralMap s) = g')
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.Γ (pullback f (strictHenselizationStructuralMap s)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj
      ((upperStar (ModuleCat.{u + 1} Λ)
        (pullback.fst f (strictHenselizationStructuralMap s))).obj F) ⟶
      ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 X'))) :=
  globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i
      ((upperStar (ModuleCat.{u + 1} Λ)
        (pullback.fst f (strictHenselizationStructuralMap s))).obj F) ≫
    (Sheaf.Γ X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) i
        (pullback.fst f (strictHenselizationStructuralMap s)) g' hi.symm).inv.app F) ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X')
        (Scheme.Etale.mk (𝟙 X')) Over.mkIdTerminal)).hom.app _

theorem strictLocalFibreRestriction_compatibility
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
    (t : Spec (.of Ω) ⟶ strictHenselizationScheme s)
    (ht : ∀ j : SmallModel.{u} (strictHenselizationNeighbourhoods s),
      t ≫ (strictHenselizationCone s).π.app (op (op j)) ≫
        (Spec (unop ((equivSmallModel.{u}
          (strictHenselizationNeighbourhoods s)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2.left)
    (i : X' ⟶ pullback f (strictHenselizationStructuralMap s))
    (hi : i ≫ pullback.fst f (strictHenselizationStructuralMap s) = g')
    (hi' : i ≫ pullback.snd f (strictHenselizationStructuralMap s) = f' ≫ t)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
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
          pullbackSymmetry_hom_comp_snd]) ≫ strictLocalFibreRestriction Λ i hi F =
      geometricFibreSectionRestriction Λ sq F
        ((AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2
```

## New

The Sheaf module is withdrawn through deleted.txt. The node now attaches to the
existing declarations in the unchanged adopted source module:

```lean
noncomputable def strictLocalFibreRestriction
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {g' : X' ⟶ X} {f : X ⟶ Y}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {s : Spec (.of Ω) ⟶ Y}
    (i : X' ⟶ pullback f (strictLocalizationToBase s))
    (hi : i ≫ pullback.fst f (strictLocalizationToBase s) = g')
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.Γ (pullback f (strictLocalizationToBase s)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj
      ((upperStar (ModuleCat.{u + 1} Λ)
        (pullback.fst f (strictLocalizationToBase s))).obj F) ⟶
      ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 X'))) :=
  globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i
      ((upperStar (ModuleCat.{u + 1} Λ)
        (pullback.fst f (strictLocalizationToBase s))).obj F) ≫
    (Sheaf.Γ X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) i
        (pullback.fst f (strictLocalizationToBase s)) g' hi.symm).inv.app F) ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X')
        (Scheme.Etale.mk (𝟙 X')) Over.mkIdTerminal)).hom.app _

theorem strictLocalFibreRestriction_compatibility
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
    (t : Spec (.of Ω) ⟶ strictLocalization s)
    (ht : ∀ j : SmallModel.{u} (strictHenselizationNeighbourhoods s),
      t ≫ (strictHenselizationAffineCone s).π.app (op (op j)) ≫
        (Spec (unop ((equivSmallModel.{u}
          (strictHenselizationNeighbourhoods s)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2.left)
    (i : X' ⟶ pullback f (strictLocalizationToBase s))
    (hi : i ≫ pullback.fst f (strictLocalizationToBase s) = g')
    (hi' : i ≫ pullback.snd f (strictLocalizationToBase s) = f' ≫ t)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
    qcqsStrictLocalSectionRestriction Λ f s F j ≫ strictLocalFibreRestriction Λ i hi F =
      geometricFibreSectionRestriction Λ sq F
        ((AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2
```

The sole consumer retains its exact theorem signature, visibility, docstring and
public imports. Its new local r is the full former definition body, with the same
scheme maps, inverse-image composition isomorphism and terminal evaluation. Its
proof constructs the witness explicitly and uses no arbitrary existence witness
for this isomorphism. The invertibility and compatibility arguments are complete.

## Users

The current tools/downstream.py census with --uses strictLocalFibreRestriction
lists one downstream module. A source search over lean/Sheaf, lean/WeilConjectures
and quarantine finds no further consumer of the retired module or declarations.
The corresponding adopted consumer uses its unchanged adopted counterpart.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux | unclaimed | Remove the private import; construct r and prove compatibility directly; exact original signature and all public imports retained. |

No target signature or definition visible in a target statement changes. The
retired module was privately imported by the sole consumer. No source-library
file is changed. The unit sk-lem-universal-datum has no realized statement or step
on this node; its route and the chapter route are unchanged. This is the listed
retirement, with its actual consumer replacement argument, rather than pruning
based on an empty importer census.

The compatibility node statement and lean.statement record the adopted theorem's
exact signature, and statement_change audits the sole current DAG citer. Its
proof uses the adopted strictLocal_section_pullback. The consumer node records
the local construction and direct general composition argument and removes the
obsolete dependency on the retired small-model theorem. No DAG node is deleted.

## Status

landed 20261022T022950-L-766828 2026-10-22 (merge of deliver/E1/Sheaf.AlgebraicGeometry.StrictLocalFibreRestrictionCompatibility)
