/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
public import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import WeilConjectures.AlgebraicGeometry.StrictLocalSectionPullback

/-! # Compatibility of the constructed strict-local fibre restriction

## References

* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
open Scheme

/-- Restriction along an explicit map to the strict-local pullback, followed by
inverse-image composition and evaluation at the identity etale object. -/
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

/-- Compatibility uses only the two projections of i and the pointed limit-leg
identities, and asserts neither continuity nor invertibility. -/
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
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2 := by
  have h := strictLocal_section_pullback Λ sq F t ht i hi' hi j
  unfold strictLocalFibreRestriction
  simp only [← Category.assoc] at h ⊢
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

end AlgebraicGeometry.Etale
