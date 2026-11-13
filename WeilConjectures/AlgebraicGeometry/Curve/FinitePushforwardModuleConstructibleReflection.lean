/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.ConstructibleSheaf.Monoidal
import all WeilConjectures.AlgebraicGeometry.Curve.FinitePushforwardCoefficientControl
import WeilConjectures.AlgebraicGeometry.Curve.FinitePushforwardModuleLocallyConstantStrata

/-! # Constructibility reflected by finite direct image on curves

Source: Stacks Project, Tags 095K, 0959, 04DZ, and 095G;
finite direct-factor refinement of the argument for Tag 0A5D.
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Finite generation descends through the finite direct-image counit. -/
private theorem finite_module_stalks {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : Scheme.IsFiniteSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)) :
    Scheme.IsFiniteSheaf F := by
  let G := (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F
  let beta := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app F
  have : Epi beta := finite_counit_epi f Λ F
  have : Scheme.IsFiniteSheaf G := h
  have hmid := Scheme.IsFiniteSheaf.upperStar f G
  refine ⟨fun Ω _ _ s ↦ ?_⟩
  have : CategoryTheory.Limits.HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    CategoryTheory.Limits.hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have : ((Scheme.pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      ((Scheme.pointSmallEtale s).skyscraperSheafAdjunction)
  have hsurj := (ModuleCat.epi_iff_surjective
    ((Scheme.pointSmallEtale s).sheafFiber.map beta)).mp inferInstance
  have hfg : Module.Finite Λ
      (((Scheme.pointSmallEtale s).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj G)) :=
    (ModuleCat.isFinitelyGenerated_iff _).mp (hmid.isFinitelyGenerated_sheafFiber Ω s)
  exact (ModuleCat.isFinitelyGenerated_iff _).mpr
    (Module.Finite.of_surjective (hM := hfg)
      ((Scheme.pointSmallEtale s).sheafFiber.map beta).hom hsurj)

/-- Finite direct image reflects module constructibility on Noetherian curves.
Source: Stacks Project, Tags 095K (finite morphism stratification), 0959 (finite
base change), 095G (pullback), and 0A5D (the assertion-transfer argument). -/
theorem Scheme.isConstructibleSheaf_of_finite_lowerStar_module
    {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of k)) [IsCurve g] [IsFinite f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : Scheme.IsConstructibleSheaf
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)) :
    Scheme.IsConstructibleSheaf F := by
  have hfinite : Scheme.IsFiniteSheaf F := finite_module_stalks Λ f F h.isFiniteSheaf
  obtain ⟨S, hS⟩ :=
    Scheme.exists_locallyConstant_stratification_of_finite_lowerStar_module Λ f g F h
  refine ⟨S, fun i ↦ ?_⟩
  exact
    { toIsLocallyConstantSheaf := hS i
      toIsFiniteSheaf := Scheme.IsFiniteSheaf.upperStar (S.immersion i) F }
end AlgebraicGeometry
