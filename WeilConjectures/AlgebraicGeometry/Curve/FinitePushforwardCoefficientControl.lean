/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CurveCoefficientPair
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Curve.FinitePushforwardConstructibleDescent
import WeilConjectures.AlgebraicGeometry.ConstructibleIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.SixFunctors.Finite.Stalk

/-! # Coefficient hypotheses for finite direct images

Source: Stacks Project, Lemma 0A5D and Tags 03QP, 095G, 09BH.
(blueprint: g1-finite-pushforward-coefficient-control)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The finite direct-image counit is stalkwise a split product projection. -/
private theorem finite_counit_epi {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Epi ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app F) := by
  classical
  have : CategoryTheory.Limits.HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    CategoryTheory.Limits.hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  let beta := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app F
  have hstalk (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) :
      Epi ((Scheme.pointSmallEtale s).sheafFiber.map beta) := by
    let D := fun t : Scheme.Hom.GeometricFiber f (s ≫ f) ↦
      (Scheme.pointSmallEtale t.1).sheafFiber.obj F
    have : CategoryTheory.Limits.HasLimit (Discrete.functor D) :=
      CategoryTheory.Limits.HasLimitsOfShape.has_limit _
    have hrestrict : Epi (Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f
        (s ≫ f) ⟨s, rfl⟩ F) := by
      have he : (Etale.stalkIsoPi (ModuleCat.{u + 1} Λ) f (s ≫ f) F).hom ≫
          CategoryTheory.Limits.Pi.π D ⟨s, rfl⟩ = _ :=
        CategoryTheory.Limits.Pi.lift_π _ _
      rw [← he]
      infer_instance
    exact epi_of_epi_fac
      (Etale.stalkRestrict_eq_counit (ModuleCat.{u + 1} Λ) f s F).symm
  have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1} (C := X.Etale)
  let hpoints := Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale X
  apply (hpoints.jointlyReflectEpimorphisms (ModuleCat.{u + 1} Λ)).epi_iff beta |>.mpr
  rintro ⟨-, ⟨x⟩⟩
  let e := (Scheme.pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso.{u + 1}
    (ModuleCat.{u + 1} Λ)
  have := hstalk _ (X.algClosurePoint x)
  let Φ := Scheme.pointSmallEtale (X.algClosurePoint x)
  change Epi ((Φ.ulift.{u + 1}).sheafFiber.map beta)
  rw [← epi_comp_iff_of_isIso _ (e.hom.app F)]
  change Epi (((Scheme.pointSmallEtale (X.algClosurePoint x)).ulift.{u + 1}).sheafFiber.map
    beta ≫ e.hom.app F)
  erw [e.hom.naturality beta]
  infer_instance

end AlgebraicGeometry
