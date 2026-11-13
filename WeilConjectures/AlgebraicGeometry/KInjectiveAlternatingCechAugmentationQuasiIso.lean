/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
import WeilConjectures.AlgebraicGeometry.InjectiveTermsAlternatingCechAugmentation
import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalHomotopy
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.AlgebraicGeometry.AlternatingCechComputes
import WeilConjectures.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions

/-! # Čech augmentation of a K-injective complex

## References

* Stacks Project, Cohomology, Lemma 08C1 and Tag 01EP.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The finite-cover Čech augmentation is a quasi-isomorphism on every K-injective
complex. Injectivity of its individual terms is not required. -/
theorem kInjective_alternatingCech_augmentation_quasiIso
    (X : Scheme.{u}) (r : ℕ) (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [J.IsKInjective] :
    QuasiIso ((alternatingCechAugmentation U).app J) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u} C).obj J
  let j : J ⟶ I := (CochainComplex.toKInjectiveResolution.{u} C).app J
  have hj : QuasiIso j :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} C J).2
  have : I.IsKInjective := inferInstance
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff j).mp hj
  let S := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let T := alternatingCechTotalFunctor U
  have hS : QuasiIso (S.map j) := by
    rw [← he]
    exact (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomotopyEquiv e
      |>.quasiIso_hom
  have hT : QuasiIso (T.map j) := by
    obtain ⟨h₁⟩ := alternatingCechTotal_map_homotopy U e.homotopyHomInvId
    obtain ⟨h₂⟩ := alternatingCechTotal_map_homotopy U e.homotopyInvHomId
    change Homotopy (T.map (e.hom ≫ e.inv)) (T.map (𝟙 J)) at h₁
    change Homotopy (T.map (e.inv ≫ e.hom)) (T.map (𝟙 I)) at h₂
    let eT : HomotopyEquiv (T.obj J) (T.obj I) :=
      { hom := T.map e.hom
        inv := T.map e.inv
        homotopyHomInvId := by
          rw [T.map_comp, T.map_id] at h₁
          exact h₁
        homotopyInvHomId := by
          rw [T.map_comp, T.map_id] at h₂
          exact h₂ }
    rw [← he]
    exact eT.quasiIso_hom
  have hI : QuasiIso ((alternatingCechAugmentation U).app I) :=
    injectiveTerms_alternatingCech_augmentation_quasiIso X r U hU I
      (fun n ↦ inferInstance)
  have hcomp : QuasiIso
      (((alternatingCechAugmentation U).app J) ≫ T.map j) := by
    rw [← (alternatingCechAugmentation U).naturality j]
    change QuasiIso (S.map j ≫ (alternatingCechAugmentation U).app I)
    infer_instance
  exact (quasiIso_iff_comp_right ((alternatingCechAugmentation U).app J) (T.map j)).mp
    hcomp

end AlgebraicGeometry
