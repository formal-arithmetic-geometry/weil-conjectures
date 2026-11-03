/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PadicAlgClSections

/-! # Connected constant-coefficient sections, with finite pushforward in degree zero
Source: blueprint lem-fd-cohomology-affine-line-character, constant degree-zero sections.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ArtinSchreierTrace
section
attribute [local instance] Sheaf.monoidalCategory

end

set_option maxHeartbeats 800000 in
-- Comparing the site monoidal unit with sheafified constant integers is expensive.
open MonObj in
set_option maxHeartbeats 800000 in
-- Comparing regular-module coordinates unfolds the geometric coefficient evaluation.
set_option maxHeartbeats 800000 in
-- Specializing the generic comparison checks the concrete field-evaluation functor.
/-- Degree zero of a pushed-forward regular coefficient has one coefficient dimension
when its source is connected and quasi-compact quasi-separated.
Source: the constant-section step of lem-fd-cohomology-affine-line-character
(blueprint: lem-fd-cohomology-connected-pushforward-zero).
Proof: degree-zero derived sections are underived sections. The composition
isomorphism identifies sections of f_*Λ with sections of Λ on Y. On a connected
qcqs scheme the continuous-function description makes every coefficient section
constant. The coefficient unit is therefore bijective on terminal sections.
Exact field evaluation and the degree-zero derived comparison identify these
sections with the canonical lifted coefficient line. -/
theorem qlbar_connected_pushforward_zero_iso
    (ℓ : ℕ) [Fact ℓ.Prime] (K : Type u) [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y] [ConnectedSpace Y]
    (f : Y ⟶ X) (a : X ⟶ Spec (.of K)) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (PadicAlgCl ℓ)) 0).obj
      ((WeilConjectures.condensedQbarOrdinarySections ℓ K a).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((ProEtale.CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) f).obj
            (Mod.regular (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))))) ≅
        ModuleCat.of (PadicAlgCl ℓ) (ULift.{u + 1} (PadicAlgCl ℓ))) := by
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  let F := ProEtale.CondensedRing.lowerStar Λ a
  let G := ProEtale.CondensedRing.lowerStar Λ f
  let J := ProEtale.CondensedRing.lowerStar Λ (f ≫ a)
  let E := ProEtale.CondensedQbarGeometricEvaluation.fieldFiber K ℓ
  let N := Mod.regular (ProEtale.padicAlgClRingObj Y ℓ)
  obtain ⟨eX⟩ := derived_zero_evaluation_iso F E (G.obj N)
  obtain ⟨eY⟩ := derived_zero_evaluation_iso J E N
  obtain ⟨e₀⟩ := connected_unit_zero_iso ℓ K Y (f ≫ a)
  exact ⟨eX ≪≫ E.mapIso ((ProEtale.CondensedRing.lowerStarComp Λ f a).app N) ≪≫
    eY.symm ≪≫ e₀⟩
end AlgebraicGeometry.ArtinSchreierTrace
