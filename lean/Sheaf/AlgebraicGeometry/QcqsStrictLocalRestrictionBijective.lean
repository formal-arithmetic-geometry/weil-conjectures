/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SmallStrictLocalSectionMaps
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

import Sheaf.AlgebraicGeometry.StrictLocalModuleSectionsSetTransport
import WeilConjectures.AlgebraicGeometry.CofilteredEtaleLimitSections
import WeilConjectures.AlgebraicGeometry.StrictHenselizationBaseChangeCone

/-! # Bijectivity of strict-local restriction maps
Source: Stacks Project, Tag 03Q9.
(blueprint: lem-weil-pbc-strict-local-module-restriction-bijective)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- The underlying function of a linear map satisfying the representative formula is bijective.
This asserts only invertibility of an already constructed map, not its existence.
Source: Stacks Project, Tag 03Q9, degree zero; Tags 03D3 and 03D7 for inverse images.
(blueprint: lem-weil-pbc-strict-local-module-restriction-bijective).

Proof: Forget modules. The forgetful functor preserves filtered colimits, hence identifies
this map's source with the set stalk, with the same germ maps. The canonical module/set
inverse-image comparison and pullback symmetry give the target equivalence, with its unit
formula. Compute the stalk as the colimit over small affine pointed neighbourhoods.
Their base changes form a limit cone with qcqs stages and affine transitions, so
`cofilteredLimitSections` gives the colimit cocone of strict-local sections. Its graph maps
agree with the transported small-model maps by their two projections. The unique colimit
comparison is bijective. The assumed representative equations and coefficient transport
show that the conjugated linear map agrees on every component with this comparison.
Joint surjectivity of the components proves equality, and the source and target bijections
then give bijectivity of the original linear map.
The argument uses qcqs continuity but no properness or torsion, and includes the empty
source and zero coefficient ring. -/
theorem bijective_qcqsStrictLocalRestriction_of_formula
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
        (Scheme.Etale.mk (𝟙 _)) Over.mkIdTerminal)).inv.app _) :
    Function.Bijective (ConcreteCategory.hom a) := by
  classical
  let U := forget (ModuleCat.{u + 1} Λ)
  let H := (sheafCompose X.smallEtaleTopology U).obj F
  let P := (lowerStar (ModuleCat.{u + 1} Λ) f).obj F
  let : PreservesFilteredColimitsOfSize.{u, u} U :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} U
  let γ := (Scheme.pointSmallEtale s).sheafFiberCompIso U
  let e := strictLocalModuleSectionsSetEquiv Λ f s F
  have he := strictLocalModuleSections_set_transport Λ f s F
  let Pset := (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
    (Type (u + 1)) (Y.smallGrothendieckTopology @Etale)
    (X.smallGrothendieckTopology @Etale)).obj H).obj
  let N := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
    strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
      (fun n : (pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)
  let : N.Initial := (strictHenselization_properties s).1
  let B := strictHenselizationEtaleDiagram s ⋙
    MorphismProperty.Over.pullback @Etale ⊤ f
  let stalkCocone := ((pointSmallEtale s).presheafFiberCocone Pset).whisker N.op
  have hcStalk : IsColimit stalkCocone :=
    (Functor.Final.isColimitWhiskerEquiv N.op _).symm
      ((pointSmallEtale s).isColimitPresheafFiberCocone Pset)
  have hcStalk' : IsColimit (show Cocone (B.op ⋙ H.obj) from stalkCocone) := hcStalk
  obtain ⟨π, hπ, hp, hf⟩ := strictHenselizationBaseChangeCone_exists f s
  let c := Cone.mk _ π
  let := (strictHenselization_properties s).2.1
  have hAff (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
      IsAffine ((strictHenselizationEtaleDiagram s).obj j).left := by
    change IsAffine (Spec _)
    infer_instance
  let hComp (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
      CompactSpace (B.obj j).left := by
    let : IsAffine ((strictHenselizationEtaleDiagram s).obj j).left := hAff j
    let : CompactSpace ((strictHenselizationEtaleDiagram s).obj j).left :=
      inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace
      (Y := ((strictHenselizationEtaleDiagram s).obj j).left)
      (pullback.fst ((strictHenselizationEtaleDiagram s).obj j).hom f)
  let hQS (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
      QuasiSeparatedSpace (B.obj j).left := by
    let : IsAffine ((strictHenselizationEtaleDiagram s).obj j).left := hAff j
    let : QuasiSeparatedSpace ((strictHenselizationEtaleDiagram s).obj j).left :=
      inferInstance
    exact quasiSeparatedSpace_of_quasiSeparated
      (Y := ((strictHenselizationEtaleDiagram s).obj j).left)
      (pullback.fst ((strictHenselizationEtaleDiagram s).obj j).hom f)
  let hTrans {j k : SmallModel.{u} (strictHenselizationNeighbourhoods s)}
      (a : j ⟶ k) : IsAffineHom (B.map a).left := by
    let : IsAffine ((strictHenselizationEtaleDiagram s).obj j).left := hAff j
    let : IsAffine ((strictHenselizationEtaleDiagram s).obj k).left := hAff k
    change IsAffineHom (pullback.lift _ _ _)
    exact MorphismProperty.pullbackLift_fst_snd
      (P := @IsAffineHom) f
        (MorphismProperty.Over.w ((strictHenselizationEtaleDiagram s).map a)).symm
        (isAffineHom_of_isAffine
          (X := ((strictHenselizationEtaleDiagram s).obj j).left)
          (Y := ((strictHenselizationEtaleDiagram s).obj k).left) _)
  have hc := cofilteredLimitSections B c
    (pullback.snd (strictHenselizationStructuralMap s) f) hp H hπ.some
  let comparison := hcStalk'.coconePointUniqueUpToIso hc.some
  have hcomparison (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
      stalkCocone.ι.app (op j) ≫ comparison.hom =
        (limitSectionCocone B c (pullback.snd (strictHenselizationStructuralMap s) f)
          hp H).ι.app (op j) :=
    hcStalk'.comp_coconePointUniqueUpToIso_hom hc.some (op j)
  have hσ (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
      limitSectionMap B c (pullback.snd (strictHenselizationStructuralMap s) f) hp j =
        smallStrictHenselizationSectionMap f s j := by
    apply MorphismProperty.Over.Hom.ext
    change pullback.lift _ _ _ = pullback.lift _ _ _
    apply pullback.hom_ext
    · simp only [pullback.lift_fst]
      change π.app j = smallStrictHenselizationBaseChangeMap f s j
      apply pullback.hom_ext
      · exact (hf j).trans (smallStrictHenselizationBaseChangeMap_fst f s j).symm
      · exact (hp j).trans (smallStrictHenselizationBaseChangeMap_snd f s j).symm
    · simp only [pullback.lift_snd]
      rfl
  have hFormula (j : SmallModel.{u} (strictHenselizationNeighbourhoods s))
      (z : H.obj.obj (op (B.obj j))) :
      comparison.hom (stalkCocone.ι.app (op j) z) =
        ((etaleSetPullback (pullback.snd (strictHenselizationStructuralMap s) f)).obj
          H).obj.map (smallStrictHenselizationSectionMap f s j).op
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤
              (pullback.snd (strictHenselizationStructuralMap s) f))
            (Type (u + 1)) (X.smallGrothendieckTopology @Etale)
            ((pullback (strictHenselizationStructuralMap s) f).smallGrothendieckTopology
              @Etale)).unit.app H).hom.app (op (B.obj j)) z) := by
    have hs := congrArg (fun a ↦ a z) (hcomparison j)
    change comparison.hom (stalkCocone.ι.app (op j) z) =
      ((etaleSetPullback (pullback.snd (strictHenselizationStructuralMap s) f)).obj
        H).obj.map (limitSectionMap B c _ hp j).op _ at hs
    rw [hσ] at hs
    exact hs
  let Θ := comparison.hom
  have hbij := ConcreteCategory.bijective_of_isIso comparison.hom
  let b := fun t ↦ e (ConcreteCategory.hom a ((γ.hom.app P) t))
  have hb : b = Θ := by
    have hcomponents : ∀ j z, b (stalkCocone.ι.app (op j) z) =
        comparison.hom (stalkCocone.ι.app (op j) z) := by
      intro j z
      rw [hFormula]
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
      exact he j z
    funext z
    obtain ⟨j, z, rfl⟩ := Types.jointly_surjective_of_isColimit hcStalk' z
    exact hcomponents j.unop z
  have hb' : Function.Bijective b := hb ▸ hbij
  have hγbij := ConcreteCategory.bijective_of_isIso (γ.hom.app P)
  constructor
  · intro x y hxy
    obtain ⟨x', rfl⟩ := hγbij.2 x
    obtain ⟨y', rfl⟩ := hγbij.2 y
    exact congrArg (fun t ↦ (γ.hom.app P) t) (hb'.1 (congrArg e hxy))
  · intro y
    obtain ⟨x, hx⟩ := hb'.2 (e y)
    exact ⟨(γ.hom.app P) x, e.injective hx⟩

end AlgebraicGeometry.Etale
