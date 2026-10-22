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
import Sheaf.AlgebraicGeometry.StrictLocalSectionPullback

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

Proof: Apply `strictLocal_section_pullback` with q = i and the two projection
identities hi' and hi. It identifies the first two factors of the constructed
restriction with geometricFibreSectionRestriction followed by inverse terminal
evaluation. Postcompose with terminal evaluation and cancel its inverse. The
pointed limit-leg calculation and composition-unit coherence are already proved
in that theorem. No continuity or invertibility of the restriction is used,
and the argument includes empty schemes and the zero coefficient ring. -/
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
  have h := strictLocal_section_pullback Λ sq F t ht i hi' hi j
  unfold strictLocalFibreRestriction
  simp only [← Category.assoc] at h ⊢
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

end AlgebraicGeometry.Etale
