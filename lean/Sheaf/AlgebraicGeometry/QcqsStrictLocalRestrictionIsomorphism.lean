/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.SmallStrictLocalSectionMaps
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

import Sheaf.AlgebraicGeometry.ModuleSectionsIsoTransport

/-! # Strict-local module restriction: one step of the comparison

Source: Stacks Project, Tag 03Q9, degree zero and canonical restriction maps.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A linear map with the strict-local representative formula is invertible.
This asserts only invertibility of an already constructed map, not its existence.
Source: Stacks Project, Tag 03Q9, degree zero; Tags 03D3 and 03D7 for inverse images.
(blueprint: lem-weil-pbc-strict-local-module-restriction-isomorphism).

Proof: Forget modules and identify the set stalk with the underlying module stalk,
compatibly with germs. Base change the canonical isomorphism from the small ring
colimit to the full affine ring colimit, and compose with pullback symmetry. This
identifies the small-model fibre product with the full strict-local fibre product
over X. The general module section transport theorem gives a target equivalence
and its unit/restriction formula. The definition of the small-model leg identifies
its graph with the transported full-model leg. Thus the assumed representative
equations identify the conjugated map with the unique canonical set comparison.
The official set comparison is bijective. Cancel the source and target bijections
and apply the concrete-category criterion for an isomorphism of modules.
This works without properness or torsion, including empty X and the zero ring. -/
theorem isIso_qcqsStrictLocalRestriction_of_formula
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (a : (Scheme.pointSmallEtale s).sheafFiber.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ⟶
      (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F))
    (ha : ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
      (Scheme.pointSmallEtale s).toPresheafFiber
        ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ a =
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
    (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).unit.app F).hom.app
      (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) ≫
    ((upperStar (ModuleCat.{u + 1} Λ)
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F).obj.map
        (MorphismProperty.Over.homMk
    (pullback.lift
      ((pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
        Scheme.smallStrictHenselizationBaseChangeMap f s j)
      (𝟙 _)
      (by
        change (pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
          Scheme.smallStrictHenselizationBaseChangeMap f s j ≫ pullback.snd _ f = _
        simp only [Scheme.smallStrictHenselizationBaseChangeMap_snd,
          pullbackSymmetry_hom_comp_snd, Category.id_comp]))
    (pullback.lift_snd _ _ _)).op ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
          (pullback f (Scheme.strictHenselizationStructuralMap s)))
        (Scheme.Etale.mk (𝟙 _)) Over.mkIdTerminal)).inv.app _) : IsIso a := by
  classical
  let U := forget (ModuleCat.{u + 1} Λ)
  let H := (sheafCompose X.smallEtaleTopology U).obj F
  let P := (lowerStar (ModuleCat.{u + 1} Λ) f).obj F
  let : PreservesFilteredColimitsOfSize.{u, u} U :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} U
  let γ := (Scheme.pointSmallEtale s).sheafFiberCompIso U
  let τ := pullback.map (Scheme.strictHenselizationStructuralMap s) f
    (Scheme.strictLocalizationToBase s) f
    (Spec.map (Scheme.smallStrictHenselizationColimitIso s).inv) (𝟙 X) (𝟙 Y)
    (by simpa using (Scheme.smallStrictLocalization_toBase s).symm) (by simp)
  have : IsIso τ := by dsimp [τ]; infer_instance
  let σ := pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s) ≪≫ asIso τ
  have hg : σ.hom ≫ pullback.snd (Scheme.strictLocalizationToBase s) f =
      pullback.fst f (Scheme.strictHenselizationStructuralMap s) := by
    simp [σ, τ, Category.assoc]
  have hleg (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
      σ.hom ≫ Scheme.strictHenselizationBaseChangeMap f s j =
        (pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
          Scheme.smallStrictHenselizationBaseChangeMap f s j := by
    simp only [σ, Iso.trans_hom, asIso_hom,
      Scheme.smallStrictHenselizationBaseChangeMap, Category.assoc, τ]
  obtain ⟨e, he⟩ := exists_moduleSectionsIsoTransport Λ σ
    (pullback.snd (Scheme.strictLocalizationToBase s) f)
    (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) hg F
  obtain ⟨_, Θ, _, hbij, huniq⟩ := sets_pushforward_stalk_strictHenselization f H s
  let b := fun t ↦ e (ConcreteCategory.hom a ((γ.hom.app P) t))
  have hb : b = Θ := by
    apply huniq
    intro j z
    dsimp only [b]
    have hγ := ConcreteCategory.congr_hom
      ((Scheme.pointSmallEtale s).toPresheafFiber_presheafFiberCompIso_hom_app U
        ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2
        P.obj) z
    change (γ.hom.app P) _ = _ at hγ
    erw [hγ]
    have h := ConcreteCategory.congr_hom (ha j) z
    change ConcreteCategory.hom a _ = _ at h
    erw [h]
    have hv : Scheme.strictHenselizationBaseChangeMap f s j ≫ pullback.snd _ f =
        pullback.snd (Scheme.strictLocalizationToBase s) f := pullback.lift_snd _ _ _
    have ht := he (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
      ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))
      (Scheme.strictHenselizationBaseChangeMap f s j) hv z
    dsimp only at ht
    simp only [hleg j] at ht
    convert ht using 1 <;> simp only [Scheme.strictHenselizationSectionMap, H, U] <;> rfl
  have hb' : Function.Bijective b := hb ▸ hbij
  have hγbij := ConcreteCategory.bijective_of_isIso (γ.hom.app P)
  apply (ConcreteCategory.isIso_iff_bijective a).mpr
  exact (Function.Bijective.of_comp_iff _ hγbij).mp
    ((e.comp_bijective _).mp hb')

end AlgebraicGeometry.Etale
