/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
import WeilConjectures.AlgebraicGeometry.ScalarUnitCohomologyCoordinates
import WeilConjectures.AlgebraicGeometry.ExternalCupScalarBalance
import WeilConjectures.AlgebraicGeometry.PicardExternalCupUnitComparison

/-! # Scalar normalization of external cup products with unit coefficients

## References

* Stacks Project, Varieties, Tag 0BED
* Stacks Project, Cohomology on Sites, Tag 03FD
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme
open Modules

/-- Unit-coefficient comparison carries cup products with scalar degree-zero classes
to scalar multiples of projection pullbacks. This is a comparison of individual cup
products, without a Kunneth or spanning assertion and without properness assumptions
(Stacks, Tag 0BED; Tag 03FD). -/
theorem picard_external_cup_scalar_comparison (k : Type u) [Field k] (X Y : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (hX : Function.Bijective (scalarMap f ⊤))
    (hY : Function.Bijective (scalarMap g ⊤)) :
    let F := SheafOfModules.unit X.ringCatSheaf
    let G := SheafOfModules.unit Y.ringCatSheaf
    ∃ (eX : scalarCohomology f F 1 ≃+ Sheaf.H (structureSheafAb X) 1)
      (eY : scalarCohomology g G 1 ≃+ Sheaf.H (structureSheafAb Y) 1)
      (eP : scalarCohomology (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) 1
        ≃+ Sheaf.H (structureSheafAb (pullback f g)) 1)
      (dX : scalarCohomology f F 0 ≃ₗ[k] k)
      (dY : scalarCohomology g G 0 ≃ₗ[k] k),
      (∀ (a : scalarCohomology f F 1) (b : scalarCohomology g G 0),
        eP (externalCup f g F G 1 0 a b) =
          structureSheafCohomologyPullback (pullback.fst f g) 1 (eX (dY b • a))) ∧
      (∀ (a : scalarCohomology f F 0) (b : scalarCohomology g G 1),
        eP (externalCup f g F G 0 1 a b) =
          structureSheafCohomologyPullback (pullback.snd f g) 1 (eY (dX a • b))) := by
  obtain ⟨dX, hdX⟩ := scalar_unit_cohomology_coordinates f hX
  obtain ⟨dY, hdY⟩ := scalar_unit_cohomology_coordinates g hY
  obtain ⟨eX, eY, eP, heX, heY⟩ := picard_external_cup_unit_comparison k X Y f g
  refine ⟨eX, eY, eP, dX, dY, ?_, ?_⟩
  · intro a b
    have hb : b = dY b • scalarUnitCohomologyClass g := by
      exact (dY.symm_apply_apply b).symm.trans (hdY (dY b))
    calc
      eP (externalCup f g _ _ 1 0 a b) =
          eP (externalCup f g _ _ 1 0 a (dY b • scalarUnitCohomologyClass g)) := by
            exact congrArg (fun b' ↦ eP (externalCup f g _ _ 1 0 a b')) hb
      _ = eP (externalCup f g _ _ 1 0 (dY b • a) (scalarUnitCohomologyClass g)) := by
            exact congrArg eP (external_cup_scalar_balance f g _ _ 1 0 (dY b) a _)
      _ = structureSheafCohomologyPullback (pullback.fst f g) 1 (eX (dY b • a)) :=
        heX (dY b • a)
  · intro a b
    have ha : a = dX a • scalarUnitCohomologyClass f := by
      exact (dX.symm_apply_apply a).symm.trans (hdX (dX a))
    calc
      eP (externalCup f g _ _ 0 1 a b) =
          eP (externalCup f g _ _ 0 1 (dX a • scalarUnitCohomologyClass f) b) := by
            exact congrArg (fun a' ↦ eP (externalCup f g _ _ 0 1 a' b)) ha
      _ = eP (externalCup f g _ _ 0 1 (scalarUnitCohomologyClass f) (dX a • b)) := by
            exact congrArg eP
              (external_cup_scalar_balance f g _ _ 0 1 (dX a) _ b).symm
      _ = structureSheafCohomologyPullback (pullback.snd f g) 1 (eY (dX a • b)) :=
        heY (dX a • b)

end AlgebraicGeometry.Scheme
