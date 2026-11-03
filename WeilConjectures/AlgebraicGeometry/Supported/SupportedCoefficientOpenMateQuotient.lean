/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Supported.SupportedLocalizationComparisons
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.BaseChange.GlobalSections

/-!
# Normalization of the ordinary supported coefficient restriction mate

Source: Stacks Project, Tags 09XP and 0F1E, the coefficient calculation in
lem-pur-supported-product-localization, step 11.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Etale

open Scheme

/-- The left mate of a right-adjoint restriction. This fixes the coefficient comparison
by the actual support restriction, including its normalization.
Source: Stacks Tag 09XP (blueprint: lem-pur-supported-coefficient-open-mate-quotient). -/
noncomputable def supportCoefficientMate
    {B : Type u₁} {C : Type u₂} {D : Type u₃}
    [Category.{v₁} B] [Category.{v₂} C] [Category.{v₃} D]
    {F : B ⥤ C} {R : C ⥤ B} {F' : B ⥤ D} {R' : D ⥤ B}
    (adj : F ⊣ R) (adj' : F' ⊣ R') (H : C ⥤ D) (r : R ⟶ H ⋙ R') :
    F' ⟶ F ⋙ H :=
  (Functor.leftUnitor F').inv ≫
    ((mateEquiv adj adj').symm
      (TwoSquare.mk _ _ _ _ ((Functor.rightUnitor R).hom ≫ r))).natTrans

private theorem supportMate_unit
    {B C D : Type*} [Category B] [Category C] [Category D]
    {F : B ⥤ C} {R : C ⥤ B} {F' : B ⥤ D} {R' : D ⥤ B}
    (adj : F ⊣ R) (adj' : F' ⊣ R') (H : C ⥤ D) (r : R ⟶ H ⋙ R') (M : B) :
    adj'.homEquiv _ _ ((supportCoefficientMate adj adj' H r).app M) =
      adj.unit.app M ≫ r.app (F.obj M) := by
  simp [supportCoefficientMate, Adjunction.homEquiv_apply]

private lemma constantUnit_terminal
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C] {Z X : Scheme.{u}}
    (i : Z ⟶ X) (M : C) :
    (constantSheafAdj X.smallEtaleTopology C
      terminalIsTerminal).unit.app M ≫
      ((sheafSections X.smallEtaleTopology C).obj
        (op (⊤_ X.Etale))).map (((upperStarLowerStarAdjunction C i).unit.app _ ≫
          (lowerStar C i).map ((Scheme.upperStarConstantSheafIso C i).hom.app M))) ≫
      (lowerStarCompSheafSectionsTerminalIso C i).hom.app _ =
    (constantSheafAdj Z.smallEtaleTopology C
      terminalIsTerminal).unit.app M := by
  let ax := constantSheafAdj X.smallEtaleTopology C terminalIsTerminal
  let az := constantSheafAdj Z.smallEtaleTopology C terminalIsTerminal
  let p := upperStarLowerStarAdjunction C i
  let e := lowerStarCompSheafSectionsTerminalIso C i
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((ax.comp p).ofNatIsoRight e) az M
  rw [Adjunction.homEquiv_unit] at h
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc] at h
  change (ax.comp p).unit.app M ≫ e.hom.app _ ≫
    ((sheafSections Z.smallEtaleTopology C).obj
      (op (⊤_ Z.Etale))).map ((Scheme.upperStarConstantSheafIso
        C i).hom.app M) = az.unit.app M at h
  rw [← h]
  simp only [Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  erw [← e.hom.naturality]
  rfl

private lemma constantUnit_global
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C] {Z X : Scheme.{u}}
    (i : Z ⟶ X) (M : C) :
    (constantSheafΓAdj X.smallEtaleTopology C).unit.app M ≫
      (Sheaf.Γ X.smallEtaleTopology C).map
        (((upperStarLowerStarAdjunction C i).unit.app _ ≫
          (lowerStar C i).map ((Scheme.upperStarConstantSheafIso C i).hom.app M))) ≫
      (lowerStarCompGlobalSectionsIso C i).hom.app _ =
    (constantSheafΓAdj Z.smallEtaleTopology C).unit.app M := by
  let nx : Sheaf.Γ X.smallEtaleTopology C ≅
      (sheafSections X.smallEtaleTopology C).obj
        (op (⊤_ X.Etale)) := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology C terminalIsTerminal
  let nz : Sheaf.Γ Z.smallEtaleTopology C ≅
      (sheafSections Z.smallEtaleTopology C).obj
        (op (⊤_ Z.Etale)) := Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology C terminalIsTerminal
  let e := lowerStarCompSheafSectionsTerminalIso C i
  have hx := (constantSheafΓAdj X.smallEtaleTopology C).unit_rightAdjointUniq_hom_app
    (constantSheafAdj X.smallEtaleTopology C terminalIsTerminal) M
  have hz := (constantSheafΓAdj Z.smallEtaleTopology C).unit_rightAdjointUniq_hom_app
    (constantSheafAdj Z.smallEtaleTopology C terminalIsTerminal) M
  have hinj : Function.Injective
      (fun f : M ⟶ (Sheaf.Γ Z.smallEtaleTopology C).obj
        ((constantSheaf Z.smallEtaleTopology C).obj M) ↦
        f ≫ nz.hom.app ((constantSheaf Z.smallEtaleTopology C).obj M)) :=
    fun f g h ↦ (cancel_mono _).1 h
  apply hinj
  simp only [nz, lowerStarCompGlobalSectionsIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.assoc]
  erw [nx.hom.naturality_assoc]
  erw [Iso.inv_hom_id_app]
  simp only [Category.comp_id]
  rw [← Category.assoc]
  erw [hx, hz]
  exact constantUnit_terminal C i M

private theorem globalPullback_eq (A : Type (u + 1)) [CommRing A]
    {T S : Scheme.{u}} (h : S ⟶ T)
    (K : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    globalSectionsUpperStarMap (ModuleCat.{u + 1} A) h K =
      (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).unit.app K) ≫
      (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} A) h).hom.app
        ((upperStar (ModuleCat.{u + 1} A) h).obj K) := by
  dsimp only [lowerStarCompGlobalSectionsIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom]
  erw [(Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal).hom.naturality_assoc]
  rfl

private theorem globalSectionsUpperStarMap_naturality (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (m : X ⟶ Y)
    {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)} (k : F ⟶ F') :
    (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)).map k ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} A) m F' =
    globalSectionsUpperStarMap (ModuleCat.{u + 1} A) m F ≫
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        ((upperStar (ModuleCat.{u + 1} A) m).map k) := by
  let eL := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} A) terminalIsTerminal
  let eK := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} A) terminalIsTerminal
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) m
  have hu := congrArg (fun φ ↦ φ.hom.app (Opposite.op (⊤_ Y.Etale))) (adj.unit.naturality k)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
  simp only [globalSectionsUpperStarMap, Category.assoc]
  rw [eL.hom.naturality_assoc k]
  change eL.hom.app F ≫ k.hom.app (Opposite.op (⊤_ Y.Etale)) ≫
      (adj.unit.app F').hom.app (Opposite.op (⊤_ Y.Etale)) ≫
      ((upperStar (ModuleCat.{u + 1} A) m).obj F').obj.map (PreservesTerminal.iso m.Etale).inv.op ≫
      eK.inv.app _ =
    eL.hom.app F ≫ (adj.unit.app F).hom.app (Opposite.op (⊤_ Y.Etale)) ≫
      ((upperStar (ModuleCat.{u + 1} A) m).obj F).obj.map (PreservesTerminal.iso m.Etale).inv.op ≫
      eK.inv.app _ ≫ (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        ((upperStar (ModuleCat.{u + 1} A) m).map k)
  rw [reassoc_of% hu]
  have hn := ((upperStar (ModuleCat.{u + 1} A) m).map k).hom.naturality
    (PreservesTerminal.iso m.Etale).inv.op
  change ((upperStar (ModuleCat.{u + 1} A) m).obj F).obj.map
      (PreservesTerminal.iso m.Etale).inv.op ≫
      ((upperStar (ModuleCat.{u + 1} A) m).map k).hom.app (Opposite.op (⊤_ X.Etale)) =
    ((lowerStar (ModuleCat.{u + 1} A) m).map ((upperStar (ModuleCat.{u + 1} A) m).map k)).hom.app
      (Opposite.op (⊤_ Y.Etale)) ≫
      ((upperStar (ModuleCat.{u + 1} A) m).obj F').obj.map
        (PreservesTerminal.iso m.Etale).inv.op at hn
  rw [← reassoc_of% hn]
  have hk := eK.inv.naturality ((upperStar (ModuleCat.{u + 1} A) m).map k)
  change ((upperStar (ModuleCat.{u + 1} A) m).map k).hom.app
    (Opposite.op (⊤_ X.Etale)) ≫ eK.inv.app _ =
    eK.inv.app _ ≫ (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        ((upperStar (ModuleCat.{u + 1} A) m).map k) at hk
  rw [hk]

private theorem constantAdjunct_pullback (A : Type (u + 1)) [CommRing A]
    {T S : Scheme.{u}} (h : S ⟶ T) (M : ModuleCat.{u + 1} A)
    (K : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (t : (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M ⟶ K) :
    (constantSheafΓAdj S.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ _
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).inv.app M ≫
          (upperStar (ModuleCat.{u + 1} A) h).map t) =
    (constantSheafΓAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ _ t ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} A) h K := by
  let C := ModuleCat.{u + 1} A
  let ax := constantSheafΓAdj T.smallEtaleTopology C
  let az := constantSheafΓAdj S.smallEtaleTopology C
  let H := upperStar C h
  let γ := lowerStarCompGlobalSectionsIso C h
  let e := Scheme.upperStarConstantSheafIso C h
  have hu : ax.unit.app M ≫ globalSectionsUpperStarMap C h
      ((constantSheaf T.smallEtaleTopology C).obj M) ≫
      (Sheaf.Γ S.smallEtaleTopology C).map (e.hom.app M) = az.unit.app M := by
    rw [globalPullback_eq]
    have hg := γ.hom.naturality (e.hom.app M)
    dsimp only [Functor.comp_map] at hg
    erw [Category.assoc, ← hg, ← Functor.map_comp_assoc]
    exact constantUnit_global C h M
  have hu' : az.unit.app M ≫ (Sheaf.Γ S.smallEtaleTopology C).map (e.inv.app M) =
      ax.unit.app M ≫ globalSectionsUpperStarMap C h
        ((constantSheaf T.smallEtaleTopology C).obj M) := by
    rw [← hu]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  change az.unit.app M ≫ (Sheaf.Γ S.smallEtaleTopology C).map (e.inv.app M ≫ H.map t) =
    (ax.unit.app M ≫ (Sheaf.Γ T.smallEtaleTopology C).map t) ≫
      globalSectionsUpperStarMap C h K
  rw [Functor.map_comp, ← Category.assoc, hu', Category.assoc]
  simpa only [Category.assoc] using congrArg (fun v ↦ ax.unit.app M ≫ v)
    (globalSectionsUpperStarMap_naturality A h t).symm

/-- The ordinary support-restriction mate preserves the closed-coefficient quotient.
Source: Stacks Tag 09XP, coefficient restriction calculation of
lem-pur-supported-product-localization, step 11.
(blueprint: lem-pur-supported-coefficient-open-mate-quotient).
Proof: apply the normalized supported-coefficient adjunction on the open scheme.
The unit formula for mates turns its transpose into the old adjunction unit followed
by support restriction. The latter is defined by the kernel inclusion and the actual
pullback of global sections. The normalization of constant-sheaf inverse image carries
the old constant adjunct to the new one. The old supported adjunction normalization
then identifies it with the pulled-back closed quotient. Injectivity of the constant
adjunction Hom equivalence gives the equality. No flatness or nonempty-support
assumption is needed, and the argument includes empty opens and zero modules. -/
theorem supportedCoefficientOpenMate_quotient (A : Type (u + 1)) [CommRing A]
    {T S B D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (hd : d.openComplement = h ⁻¹ᵁ b.openComplement) (M : ModuleCat.{u + 1} A) :
    supportedCoefficientQuotient A d M ≫
      (supportCoefficientMate (supportedCoefficientAdjunction A b)
        (supportedCoefficientAdjunction A d) (upperStar (ModuleCat.{u + 1} A) h)
        (supportTransport A h b d hd)).app M =
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).inv.app M ≫
      (upperStar (ModuleCat.{u + 1} A) h).map (supportedCoefficientQuotient A b M) := by
  let adj := supportedCoefficientAdjunction A b
  let adj' := supportedCoefficientAdjunction A d
  let H := upperStar (ModuleCat.{u + 1} A) h
  let r := supportTransport A h b d hd
  have hn := (exists_unique_supportedCoefficientAdjunction A d).choose_spec.1 M
    (H.obj ((supportedCoefficients A b).obj M))
    (adj'.homEquiv _ _ ((supportCoefficientMate adj adj' H r).app M))
  erw [Equiv.symm_apply_apply] at hn
  erw [supportMate_unit] at hn
  rw [hn, Category.assoc]
  erw [(exists_unique_supportTransport A h b d hd).choose_spec.1]
  apply (constantSheafΓAdj S.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ _ |>.injective
  rw [Equiv.apply_symm_apply, constantAdjunct_pullback]
  have hb := (exists_unique_supportedCoefficientAdjunction A b).choose_spec.1 M
    ((supportedCoefficients A b).obj M) (adj.unit.app M)
  have hid : (adj.homEquiv M ((supportedCoefficients A b).obj M)).symm (adj.unit.app M) =
      𝟙 _ := by
    apply (adj.homEquiv _ _).injective
    erw [Equiv.apply_symm_apply, Adjunction.homEquiv_apply,
      CategoryTheory.Functor.map_id, Category.comp_id]
  erw [hid, Category.comp_id] at hb
  rw [hb, Equiv.apply_symm_apply]
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry.Etale
