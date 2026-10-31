/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSystemFiniteLaws
import WeilConjectures.AlgebraicGeometry.FieldShriekSystemModelExistence
import WeilConjectures.AlgebraicGeometry.FieldShriekSystemCoordinateExistence
import WeilConjectures.AlgebraicGeometry.FieldShriekSystemEvaluationEquation

/-! # Simultaneous models and finite evaluation of the proper/open comparison

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2),
proof steps 1--3 of lem-sp-field-shriek-system-comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

/-- The simultaneous coefficient-system models admit the specified finite evaluation
of their actual proper/open comparison. This asserts neither invertibility nor either
coefficient cocycle.

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2),
lem-sp-field-shriek-system-comparison, steps 1--3
(blueprint: lem-route-field-shriek-system-realization).

Proof: for every finite coefficient subfield use the section-preserving tower
realization and geometric operations of tower_shriek_levels, together with the
coefficient-tower coordinates. The integer inclusions induce quotient maps because
ell maps to ell; their residue-class formulas give compatible ring-system maps.
Apply semilinearDerivedSections to those maps for the K-flat normalized scalar
extensions. The identity on sections supplies the restriction/pushforward square.
Its two adjunction transposes give the ordinary scalar/pullback comparison; localize
on flat-term K-flat representatives to obtain PullComparison with its representative
equation. The ringed open tensor theorem gives openIso, with inverse equal to the
open-unit mate, by its unit normalization and its generator formula on signed total
complexes. These data construct Models, rather than lifting any finite-level maps.
The identity on sections supplies restriction evaluation and finite proper-image
coordinates. Exact localization and the scalar adjunctions give ScalarEvaluation.
Evaluation of the proper mate is the finite proper counit transpose, and evaluation
of openIso is the normalized finite open tensor map. Their composite is precisely
reductionDirectImageComparison. This is the equation in EvaluationLaw. -/
theorem field_shriek_system_realization (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    ∃ D : Models P, Nonempty (EvaluationLaw P D c) := by
  classical
  obtain ⟨D⟩ := field_shriek_models_exists P
  let scalar := fun (E F : Index P) (h : E ≤ F) (T : Scheme.{u}) (n : ℕ) ↦
    (field_shriek_scalar_evaluation_exists P D h T n).some
  let support : ∀ (E : Index P) (n : ℕ), FiniteCoordinates P E c n := fun E n ↦
    { push := Iso.refl _
      sections := by
        intro M U x
        rfl }
  refine ⟨D, ⟨scalar, support, ?_⟩⟩
  exact field_shriek_evaluation_equation P c D scalar support

end AlgebraicGeometry.ProEtale.FieldShriekSystem
