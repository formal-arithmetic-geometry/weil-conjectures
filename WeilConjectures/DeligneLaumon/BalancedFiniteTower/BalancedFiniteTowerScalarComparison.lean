/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FinitePullbackStrictTowerData.FinitePullbackStrictTowerData

/-! # Balanced comparison of completed and finite scalar extension

Source: Stacks Project, Tags 03EK, 03EL and 07A4.
(blueprint: lem-a1-balanced-finite-tower-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
attribute [local irreducible] WeilConjectures.unrestrictedIntegralReductionFunctor
  WeilConjectures.CompletedTowerIndependent.pull
open WeilConjectures.CompletedTowerIndependent
open WeilConjectures.FinitePullbackStrictTowerData
open WeilConjectures.CompletedPullbackUniverseTransportData

namespace WeilConjectures.BalancedFiniteTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- Scalar extension around the coefficient projection square gives the normalized
balanced comparison, naturally on the entire category of unbounded complexes.

Source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL; steps 2, 3 and 5 of
lem-a1-balanced-finite-tower-generator-comparison.
(blueprint: lem-a1-balanced-finite-tower-scalar-comparison).

Proof: write D = g⁻¹R_Y, B = R_X, U_n = g⁻¹S_{Y,n}, V_n = S_{X,n}.
The constant-coefficient inverse-image isomorphism identifies U_n with V_n and
its projection square commutes. Apply the normalized inverse-image tensor map
in every degree to identify the finite target with
(g⁻¹P tensor_D U_n) tensor_{U_n} V_n. The strict coefficient-square calculus
identifies this with (g⁻¹P tensor_D B) tensor_B V_n: both map to
g⁻¹P tensor_D V_n by multiplying the last two coefficients after projection.
The inverse inserts 1 into the B or U_n factor. The coefficient square proves
balancing, and the tensor relations show that the composites are identities.
These are sheafified tensor maps; no surjectivity on sections is required.
Naturality of the inverse-image comparison and the strict coefficient calculus
give naturality in P and compatibility with the actual quotient transitions.
For x, b and the quotient unit the value is the finite generator multiplied
by pi_n(b), which is exactly BalancedNormalization. Totalization introduces
no permutation of homogeneous factors, and therefore preserves both differential
summands and their signs. This constructs the natural isomorphism claimed. -/
theorem balanced_scalar_comparison :
    ∃ lambda : G l E g ⋙ reductions l E X ≅ finite l E g,
      ∀ P : CochainComplex (Modules l E Y) ℤ,
        BalancedNormalization l E g P (lambda.app P) := by sorry

end WeilConjectures.BalancedFiniteTower
