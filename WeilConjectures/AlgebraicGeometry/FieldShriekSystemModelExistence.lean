/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSystemModels
import WeilConjectures.AlgebraicGeometry.FieldShriekSystemCoefficientConstruction
import WeilConjectures.AlgebraicGeometry.FieldShriekSystemGeometryExistence
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekLevels
import WeilConjectures.AlgebraicGeometry.CoefficientTowerSectionCoordinates
import WeilConjectures.AlgebraicGeometry.ScalarDataExistence

/-! # Assembly of simultaneous field coefficient models

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.proof.md (2)
(blueprint: lem-route-field-shriek-system-model-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

set_option maxHeartbeats 1600000 in
-- Assemble dependent fields without expanding the geometric constructions.
/-- The simultaneous coefficient models exist, constructed from actual quotient maps.

Source: latest blueprint, field-extension towers proof (2), simultaneous models
(blueprint: lem-route-field-shriek-system-model-existence).

Proof: choose tower bases and operations from tower_shriek_levels for every finite
coefficient field, and the section coordinates for each chosen base. Construct the
coefficient quotient maps and their natural tower maps by the quotient universal
property. Apply semilinearScalarData to each tower map. The geometric comparison
existence theorem supplies pull and open tensor comparisons for these prescribed
models. The resulting fields assemble exactly the Models structure. -/
theorem field_shriek_models_exists (P : PurityFiniteSetting.{u}) :
    Nonempty (Models P) := by
  classical
  let b := fun E : Index P ↦ (SpTowerShriek.tower_shriek_levels P.coefficients.l E.val).choose
  let o := fun E : Index P ↦
    (SpTowerShriek.tower_shriek_levels P.coefficients.l E.val).choose_spec.choose
  let z := fun E : Index P ↦
    (SpTowerCalculus.coordinates_realization P.coefficients.l E.val (b E)).some
  let a := fun (E F : Index P) (h : E ≤ F) ↦ (field_shriek_coefficients_exists P h).some
  have hs (E F : Index P) (h : E ≤ F) (T : Scheme.{u}) :
      Nonempty (Scalars P (a E F h) T) := by
    exact (SemilinearSections.semilinearScalarData.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (SpTowerShriek.B P.coefficients.l E.val T) (SpTowerShriek.tau P.coefficients.l E.val T)
      (SpTowerShriek.B P.coefficients.l F.val T) (SpTowerShriek.tau P.coefficients.l F.val T)
      (fun n ↦ ((a E F h).tower T).app (Opposite.op n))
      (fun n ↦ (((a E F h).tower T).naturality
        (homOfLE (Nat.le_succ n)).op).symm)).1
  let s := fun E F h T ↦ (hs E F h T).some
  obtain ⟨pull, openIso, open_unit⟩ := field_shriek_geometry_exists P b o a s
  exact ⟨{
    base := b
    operations := o
    coordinates := z
    coefficients := a
    scalars := s
    pull := pull
    openIso := openIso
    open_unit := open_unit }⟩

end AlgebraicGeometry.ProEtale.FieldShriekSystem
