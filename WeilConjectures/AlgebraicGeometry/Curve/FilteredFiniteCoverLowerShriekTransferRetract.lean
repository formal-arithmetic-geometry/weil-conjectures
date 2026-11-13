/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.FiniteCoverLowerShriekCoefficientCompatibility


public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

import
  WeilConjectures.AlgebraicGeometry.Curve.FiniteCoverLowerShriekCoefficientCompatibilityExtension
import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
import WeilConjectures.AlgebraicGeometry.Curve.RetractAssertions
import WeilConjectures.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.IsCurve

private theorem cohomology_retract {X : Scheme.{u}}
    {F H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (a : F ⟶ H) (b : H ⟶ F) (hab : a ≫ b = 𝟙 F) (q : ℕ)
    (x : Sheaf.H F q) : Sheaf.H.map b q (Sheaf.H.map a q x) = x := by
  rw [← Sheaf.H.map_comp_apply, hab, Sheaf.H.map_id_apply]

private theorem cohomology_injective {X : Scheme.{u}}
    {F H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (a : F ⟶ H) (b : H ⟶ F) (hab : a ≫ b = 𝟙 F) (q : ℕ) :
    Function.Injective (Sheaf.H.map a q) := by
  exact Function.LeftInverse.injective (cohomology_retract a b hab q)

private theorem cohomologyMap_surjective_retract {X Y : Scheme.{u}} (t : Y ⟶ X)
    {F H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (a : F ⟶ H) (b : H ⟶ F) (hab : a ≫ b = 𝟙 F) (q : ℕ)
    (hH : Function.Surjective (Etale.cohomologyMap t H q)) :
    Function.Surjective (Etale.cohomologyMap t F q) := by
  intro y
  let E := Etale.upperStar AddCommGrpCat.{u + 1} t
  have hE : E.map a ≫ E.map b = 𝟙 (E.obj F) := by
    rw [← E.map_comp, hab, E.map_id]
  obtain ⟨x, hx⟩ := hH (Sheaf.H.map (E.map a) q y)
  refine ⟨Sheaf.H.map b q x, ?_⟩
  rw [Etale.cohomologyMap_map, hx]
  exact cohomology_retract (E.map a) (E.map b) hE q y

private theorem cohomologyMap_bijective_retract {X Y : Scheme.{u}} (t : Y ⟶ X)
    {F H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (a : F ⟶ H) (b : H ⟶ F) (hab : a ≫ b = 𝟙 F) (q : ℕ)
    (hH : Function.Bijective (Etale.cohomologyMap t H q)) :
    Function.Bijective (Etale.cohomologyMap t F q) := by
  refine ⟨?_, cohomologyMap_surjective_retract t a b hab q hH.2⟩
  intro x y hxy
  apply cohomology_injective a b hab q
  apply hH.1
  rw [Etale.cohomologyMap_map, Etale.cohomologyMap_map, hxy]

/-- If `ρ` is a retraction of the unit `G ⟶ v_* v^* G` and the eight assertions hold for
`j_! v_* v^* G`, then they hold for `j_! G`. -/
theorem filteredFiniteCoverLowerShriekTransfer_retract {k : Type u} [Field k] [IsAlgClosed k]
    {X U V : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (j : U ⟶ X) [IsOpenImmersion j] (r : ℕ) [Fact r.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    [Scheme.IsFiniteLocallyConstantSheaf G] (v : V ⟶ U) [IsFinite v] [Etale v]
    (hH : IsCurve.Assertions (ULift.{u + 1} (ZMod r)) f
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) j).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj
          ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj G))))
    (ρ : (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj
      ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj G) ⟶ G)
    (hρ : (Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).unit.app G ≫ ρ = 𝟙 G) :
    IsCurve.Assertions (ULift.{u + 1} (ZMod r)) f
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) j).obj G) := by
  let R := ULift.{u + 1} (ZMod r)
  let J := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j
  let H := (Etale.lowerStar (ModuleCat.{u + 1} R) v).obj
    ((Etale.upperStar (ModuleCat.{u + 1} R) v).obj G)
  let E := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})
  let a : E.obj (J.obj G) ⟶ E.obj (J.obj H) := E.map (J.map ((Etale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} R) v).unit.app G))
  let b : E.obj (J.obj H) ⟶ E.obj (J.obj G) := E.map (J.map ρ)
  have hab : a ≫ b = 𝟙 (E.obj (J.obj G)) := by
    dsimp only [a, b]
    rw [← E.map_comp, ← J.map_comp, hρ]
    rw [J.map_id, E.map_id]
  obtain ⟨hconstructible, hinvertible, hprimary⟩ :=
    finiteCoverLowerShriek_coefficient_compatibility f j r G v
  have : Scheme.IsConstructibleSheaf (J.obj H) := hconstructible
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    let : Subsingleton (Sheaf.H (E.obj (J.obj H)) q) :=
      hH.subsingleton_of_two_lt q hq
    exact Function.Injective.subsingleton (cohomology_injective a b hab q)
  · intro _ q hq
    let : Subsingleton (Sheaf.H (E.obj (J.obj H)) q) :=
      hH.subsingleton_of_one_lt_of_isAffine q hq
    exact Function.Injective.subsingleton (cohomology_injective a b hab q)
  · intro p _ _ hF q hq
    let : Subsingleton (Sheaf.H (E.obj (J.obj H)) q) :=
      hH.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf p (hprimary p hF) q hq
    exact Function.Injective.subsingleton (cohomology_injective a b hab q)
  · intro _ _ q
    have : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) (J.obj H) :=
      hinvertible inferInstance
    let : Finite (Sheaf.H (E.obj (J.obj H)) q) :=
      hH.finite_of_isTorsionSheafOfInvertibleOrder q
    exact Finite.of_injective _ (cohomology_injective a b hab q)
  · intro _ _ q
    let : Finite (Sheaf.H (E.obj (J.obj H)) q) := hH.finite_of_isProper q
    exact Finite.of_injective _ (cohomology_injective a b hab q)
  · intro _ k' _ _ X' ι f' ι' h q
    have : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) (J.obj H) :=
      hinvertible inferInstance
    exact cohomologyMap_bijective_retract ι' a b hab q
      (hH.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k' h q)
  · intro _ k' _ _ X' ι f' ι' h q
    exact cohomologyMap_bijective_retract ι' a b hab q
      (hH.bijective_cohomologyMap_of_isProper k' h q)
  · intro W t _
    exact cohomologyMap_surjective_retract t a b hab 2
      (hH.surjective_cohomologyMap_of_isOpenImmersion t)

end AlgebraicGeometry.IsCurve
