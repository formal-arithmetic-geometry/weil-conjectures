/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
public import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
public import Sheaf.AlgebraicGeometry.EtaleUnitSectionRestriction
public import Sheaf.AlgebraicGeometry.SmallStrictLocalSectionMaps

/-! # Compatibility of the constructed strict-local fibre restriction

Source: Stacks Project, Tag 0EYP, canonical restrictions, and Tag 03Q9.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
open Scheme

/-- Restriction along an explicit map to the strict-local pullback, followed by
inverse-image composition and evaluation at the identity etale object.
Source: Stacks Project, Tag 0EYP, canonical restrictions.
(blueprint: lem-sbc-strict-local-fibre-restriction-compatibility). -/
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

/-- Compatibility uses only the two projections of i and the pointed limit-leg
identities, and asserts neither continuity nor invertibility.

Source: Stacks Project, Tag 0EYP, canonical restrictions, and Tag 03Q9.
(blueprint: lem-sbc-strict-local-fibre-restriction-compatibility).

Proof: apply `unitSectionRestriction_comp` to the small-model limit leg. The
composite lift has first projection f' followed by the marked point, using hi',
the first-projection formula and ht; its second projection is g', using hi and
the second-projection formula. Pullback extensionality identifies its graph with
`geometricFibreSectionLift`. Expanding unit restriction gives the representative
identity before terminal evaluation. Unfold the constructed restriction,
postcompose with terminal evaluation and cancel its inverse. No continuity or
invertibility is used; empty schemes and the zero coefficient ring are included. -/
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
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2 := by
  let V := (Scheme.AffineEtale.Spec Y).obj
    ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1
  let v := ((equivSmallModel.{u}
    (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2
  let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
  let l := (pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
    Scheme.smallStrictHenselizationBaseChangeMap f s j
  have hl : l ≫ (f.Etale.obj V).hom = p := by
    change l ≫ pullback.snd _ f = p
    simp only [l, p, Category.assoc,
      Scheme.smallStrictHenselizationBaseChangeMap_snd, pullbackSymmetry_hom_comp_snd]
  have hr := unitSectionRestriction_comp Λ i p g' hi.symm F (f.Etale.obj V) l hl
  have hg : etaleSectionGraph g' (f.Etale.obj V) (i ≫ l)
      (by rw [Category.assoc, hl, ← hi]) = geometricFibreSectionLift sq V v := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · simp only [etaleSectionGraph, geometricFibreSectionLift,
        MorphismProperty.Over.homMk_hom, Over.homMk_left, pullback.lift_fst]
      apply pullback.hom_ext
      · simp only [l, Category.assoc, pullback.lift_fst]
        rw [Scheme.smallStrictHenselizationBaseChangeMap_fst]
        simp only [← Category.assoc, pullbackSymmetry_hom_comp_fst]
        rw [hi']
        simp only [Category.assoc]
        rw [← Scheme.isoSpec_Spec_inv, ht j]
      · simp only [pullback.lift_snd]
        change (i ≫ l) ≫ (f.Etale.obj V).hom = g'
        rw [Category.assoc, hl, hi]
    · exact (etaleSectionGraph g' (f.Etale.obj V) (i ≫ l)
        (by rw [Category.assoc, hl, ← hi])).w.trans
        (geometricFibreSectionLift sq V v).w.symm
  have heq : unitSectionRestriction Λ g' F (f.Etale.obj V) (i ≫ l)
      (by rw [Category.assoc, hl, ← hi]) =
      geometricFibreSectionRestriction Λ sq F V v ≫
        (Sheaf.ΓNatIsoSheafSections _ _
          (IsTerminal.isTerminalOfObj
            (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X')
            (Scheme.Etale.mk (𝟙 X')) Over.mkIdTerminal)).inv.app
              ((upperStar (ModuleCat.{u + 1} Λ) g').obj F) := by
    unfold unitSectionRestriction
    rw [hg]
    rfl
  have h := hr.trans heq
  unfold strictLocalFibreRestriction
  simp only [← Category.assoc] at h ⊢
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

end AlgebraicGeometry.Etale
