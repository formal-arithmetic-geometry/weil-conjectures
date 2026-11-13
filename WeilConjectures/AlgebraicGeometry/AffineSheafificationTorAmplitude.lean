/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
public import WeilConjectures.AlgebraicGeometry.FiniteTorDimension
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.AlgebraicGeometry.AffineTorAmplitudeCriterion
import WeilConjectures.AlgebraicGeometry.AffineSheafificationTensorVanishingTest

/-! # Tor bounds for an affine module model

Source: Stacks Project, Tags 08CG, 08E9 and 08DX.
-/

@[expose] public section

universe u w wR

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A module complex representing the restriction of a finite-Tor-dimensional object
has finite Tor amplitude over the ring of the affine open. No pseudo-coherence or
boundedness of the representative is assumed.
Source: Stacks Project, Tag 08CG (locality), Tag 08E9(1), and Tag 08DX(2). -/
theorem finiteTorAmplitude_of_affine_sheafification (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ V : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over V))]
    (U : S.Opens) (hU : IsAffineOpen U)
    [HasDerivedCategory.{wR} (ModuleCat.{u} (S.presheaf.obj (.op U)))]
    (K : schemeDerivedCategory S)
    (P : CochainComplex (ModuleCat.{u} (S.presheaf.obj (.op U))) ℤ)
    (hP : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj K ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification S U hU).mapHomologicalComplex (.up ℤ)).obj P)))
    (hTor : HasFiniteTorDimension S K) :
    ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn
      (ModuleCat.{u} (S.presheaf.obj (.op U))) a b (DerivedCategory.Q.obj P) := by
  let : HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (moduleRings (Spec (S.presheaf.obj (.op U))).toRingedSpace)) :=
    HasDerivedCategory.standard _
  obtain ⟨a, b, hab, hvan⟩ := hTor
  refine ⟨a, b, hab, (affine_torAmplitude_iff (S.presheaf.obj (.op U)) P a b hab).mp ?_⟩
  intro G i hi
  exact affine_sheafification_tensor_vanishing_test S U hU K P hP G i
    (hvan ((Modules.pushforward (hU.isoSpec.inv ≫ U.ι)).obj G) i hi)

end AlgebraicGeometry.Scheme
