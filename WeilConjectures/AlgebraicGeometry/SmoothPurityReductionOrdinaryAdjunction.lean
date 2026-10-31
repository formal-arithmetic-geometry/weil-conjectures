/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionMonoidalData

/-! # Ordinary normalized reduction is a left adjoint

Source: Stacks 03EL; blueprint integral direct-image proof (3)
(blueprint: lem-sp-reduction-ordinary-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Normalized simultaneous reduction has a right adjoint.
Source: Stacks 03EL; blueprint integral direct-image proof (3).
(blueprint: lem-sp-reduction-ordinary-adjunction).

Proof: restrict a strict sequence module at each level along the quotient map
from the integral coefficient ring, and take the inverse limit in integral
module sheaves. A map out of the reduction of M gives at each level a map from
the scalar extension of M. Transpose it by the specified scalar adjunction.
The transition equation on generating tensors implies compatibility of these
transposes, so they form a cone and determine a map to the inverse limit.
Conversely, project a map to the inverse limit to each level and transpose
back. Scalar-adjunction naturality and the quotient transition equation show
that these maps form a strict-system morphism. The limit and scalar-adjunction
identities prove that the constructions are mutually inverse and natural in
both variables. Transport through the actual sequence-site equivalence. -/
theorem sp_reduction_ordinary_adjunction_exists
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D) :
    ∃ V : spMonoidalSystems l E T ⥤ spIntegralSectionModules l E T,
      Nonempty (spMonoidalOrdinary l E T D r ⊣ V) := by
  sorry

end AlgebraicGeometry.ProEtale
