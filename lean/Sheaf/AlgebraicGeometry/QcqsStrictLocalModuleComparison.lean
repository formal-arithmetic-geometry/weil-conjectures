/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.SmallStrictLocalSectionMaps
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.AlgebraicGeometry.StrictHenselizationBaseChangeCone
import Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionIsomorphism

/-! # The module-valued strict-local continuity comparison

Source: Stacks Project, Tag 03Q9, degree zero and the canonical restriction maps.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The terminal section of the iterated pullback corresponding to a strict-local limit leg.
The symmetry puts the base change in the orientation `X ×_Y Spec R`.
Source: Stacks Project, Tag 03Q9, proof.
(blueprint: lem-weil-pbc-qcqs-strict-local-module-comparison). -/
noncomputable def qcqsStrictLocalNeighbourhoodSection
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
    Scheme.Etale.mk (𝟙 (pullback f (Scheme.strictHenselizationStructuralMap s))) ⟶
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s)).Etale.obj
        (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
            j).1)) :=
  MorphismProperty.Over.homMk
    (pullback.lift
      ((pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
        Scheme.smallStrictHenselizationBaseChangeMap f s j)
      (𝟙 _)
      (by
        change (pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
          Scheme.smallStrictHenselizationBaseChangeMap f s j ≫ pullback.snd _ f = _
        simp only [Scheme.smallStrictHenselizationBaseChangeMap_snd,
          pullbackSymmetry_hom_comp_snd, Category.id_comp]))
    (pullback.lift_snd _ _ _)

/-- Restrict a section on the neighbourhood base change to strict-local global sections.
This is the actual module adjunction unit, followed by the specified limit leg and the
terminal-section/global-section isomorphism.
Source: Stacks Project, Tag 03Q9, proof.
(blueprint: lem-weil-pbc-qcqs-strict-local-module-comparison). -/
noncomputable def qcqsStrictLocalSectionRestriction
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
    F.obj.obj (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
      ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) ⟶
    (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj
      ((upperStar (ModuleCat.{u + 1} Λ)
        (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
    (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).unit.app F).hom.app
      (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) ≫
    ((upperStar (ModuleCat.{u + 1} Λ)
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F).obj.map
        (qcqsStrictLocalNeighbourhoodSection f s j).op ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
          (pullback f (Scheme.strictHenselizationStructuralMap s)))
        (Scheme.Etale.mk (𝟙 _)) Over.mkIdTerminal)).inv.app _

/-- The germ formula characterizing a module strict-local comparison.
Source: Stacks Project, Tag 03Q9, canonical representative restriction.
(blueprint: lem-weil-pbc-qcqs-strict-local-module-comparison). -/
def IsQcqsStrictLocalModuleComparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (a : (Scheme.pointSmallEtale s).sheafFiber.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ⟶
      (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F)) : Prop :=
  ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
    (Scheme.pointSmallEtale s).toPresheafFiber
      ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
      ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2
      ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ a =
        qcqsStrictLocalSectionRestriction Λ f s F j

/-- Qcqs continuity for module coefficients, with its canonical representative formula.
Source: Stacks Project, Tag 03Q9, degree zero; Tags 03D3 and 03D7 for inverse images.
(blueprint: lem-weil-pbc-qcqs-strict-local-module-comparison).

Proof: apply `sets_pushforward_stalk_strictHenselization` to the underlying set sheaf.
The stalk is the filtered colimit over pointed neighbourhoods. The module forgetful functor
preserves these colimits (shrink the universe of its filtered-colimit instance), so it
identifies the underlying set of the module stalk with that set stalk. The canonical
inverse-image comparison `isIso_upperStar_forget_comparison` identifies the set pullback
with the underlying set of the module pullback; its adjoint-transpose definition identifies
their units. Evaluation at the terminal object and the global-section isomorphism then
transport the set comparison to the displayed target, after pullback symmetry. Each
representative restriction is linear, and the filtered module colimit gives a linear map
with precisely the displayed germ formula. The set comparison is bijective, so this
linear map is an isomorphism. All transports preserve the units and restriction maps,
which gives `IsQcqsStrictLocalModuleComparison`. No properness is used. The empty source
and zero coefficient ring yield zero modules and the same comparison. -/
theorem exists_qcqsStrictLocalModuleComparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ e : (Scheme.pointSmallEtale s).sheafFiber.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≅
      (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F),
      IsQcqsStrictLocalModuleComparison Λ f s F e.hom := by
  classical
  let N := (equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
    Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
      (fun n : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)
  let : N.Initial := (Scheme.strictHenselization_properties s).1
  let P := ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj
  let stalkCocone := ((Scheme.pointSmallEtale s).presheafFiberCocone P).whisker N.op
  have hc : IsColimit stalkCocone :=
    (Functor.Final.isColimitWhiskerEquiv N.op _).symm
      ((Scheme.pointSmallEtale s).isColimitPresheafFiberCocone P)
  let r := qcqsStrictLocalSectionRestriction Λ f s F
  -- The concrete small-model graph has compatible projections under refinement.
  have h (j k : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s))
      (a : j ⟶ k) :
      F.obj.map ((Scheme.strictHenselizationEtaleDiagram s ⋙ f.Etale).map a).op ≫
        r j = r k := by
    let B := Scheme.strictHenselizationEtaleDiagram s ⋙ f.Etale
    let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
    let H := (upperStar (ModuleCat.{u + 1} Λ) p).obj F
    let δ := qcqsStrictLocalNeighbourhoodSection f s
    obtain ⟨π, _, hp, hf⟩ := Scheme.strictHenselizationBaseChangeCone_exists f s
    have hπ (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
        π.app j = Scheme.smallStrictHenselizationBaseChangeMap f s j := by
      apply pullback.hom_ext
      · exact (hf j).trans
          (Scheme.smallStrictHenselizationBaseChangeMap_fst f s j).symm
      · exact (hp j).trans
          (Scheme.smallStrictHenselizationBaseChangeMap_snd f s j).symm
    have hn : Scheme.smallStrictHenselizationBaseChangeMap f s j ≫ (B.map a).left =
        Scheme.smallStrictHenselizationBaseChangeMap f s k := by
      have h := π.naturality a
      change π.app k = π.app j ≫ (B.map a).left at h
      simpa only [hπ] using h.symm
    have hδ : δ j ≫ p.Etale.map (B.map a) = δ k := by
      apply MorphismProperty.Over.Hom.ext
      apply pullback.hom_ext
      · change (pullback.lift _ _ _ ≫ pullback.lift _ _ _) ≫ pullback.fst _ p =
          pullback.lift _ _ _ ≫ pullback.fst _ p
        simp only [Category.assoc, pullback.lift_fst]
        rw [pullback.lift_fst_assoc]
        simpa only [Category.assoc] using congrArg
          (fun g ↦
            (pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫ g)
          hn
      · change (pullback.lift _ _ _ ≫ pullback.lift _ _ _) ≫ pullback.snd _ p =
          pullback.lift _ _ _ ≫ pullback.snd _ p
        simp only [Category.assoc, pullback.lift_snd]
        exact pullback.lift_snd _ _ _
    change F.obj.map (B.map a).op ≫
        (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app F).hom.app
          (op (B.obj j)) ≫ H.obj.map (δ j).op ≫ _) =
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app F).hom.app
        (op (B.obj k)) ≫ H.obj.map (δ k).op ≫ _
    rw [← Category.assoc, ← Category.assoc]
    have hu :=
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app F).hom.naturality
        (B.map a).op
    change F.obj.map (B.map a).op ≫
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app F).hom.app
          (op (B.obj j)) =
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app F).hom.app
        (op (B.obj k)) ≫ H.obj.map (p.Etale.map (B.map a)).op at hu
    rw [hu]
    simp only [Category.assoc]
    rw [← H.obj.map_comp_assoc]
    rw [← op_comp, hδ]
  let c : Cocone (N.op ⋙ (CategoryOfElements.π (Scheme.pointSmallEtale s).fiber).op ⋙ P) :=
    { pt := _
      ι := { app := fun j ↦ r j.unop
             naturality := fun j k a ↦ by
               change F.obj.map
                 ((Scheme.strictHenselizationEtaleDiagram s ⋙ f.Etale).map a.unop).op ≫
                   r k.unop = r j.unop ≫ 𝟙 _
               rw [Category.comp_id]
               exact h _ _ a.unop } }
  let a := hc.desc c
  have ha : IsQcqsStrictLocalModuleComparison Λ f s F a := by
    intro j
    exact hc.fac c (op j)
  have : IsIso a := isIso_qcqsStrictLocalRestriction_of_formula Λ f s F a ha
  exact ⟨asIso a, ha⟩

end AlgebraicGeometry.Etale
