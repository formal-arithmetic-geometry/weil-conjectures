/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackCommonStageDescent

/-! # The native coefficient-enlargement square

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-native-pullback-scalar-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper

/-- Coefficient enlargement commutes with the prescribed native integral
realization components. Source: BS Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-native-pullback-scalar-coherence).

Proof: noetherianity makes native integral scalar extension exact, so its
computation counits are invertible.
Fix E <= L and an integral constructible K over E. Express isoToStage by
realizationScalarArrow, including its literal endpoint equality. Expand each integral
realization component into its source transport, R.integral, inverse completion unit,
I.derived, and inverse pullback of S.integral. The common_field equations for R and S
replace the outer scalar arrows by the specified completed coefficient changes.
The canonical rational pullback/scalar comparison is the localization of the integral
one. Match its ordinary integral pullback to the normalized ringed model by uniqueness
of the exact derived comparison with its cochain counit. Apply the whole-tower scalar
pullback completion normalization: its quotient coaugmentations use the quotient map
in the unshifted product coordinate and zero in the shifted coordinate, and commute
with every transition. Invert only the constructible completion components in I.
For the remaining ordinary scalar square, transpose along the two module adjunctions.
The insertion-of-one equation I.sections and the two coefficient_scalar equations
identify its maps on tensor-unit generators. Scalar linearity and sheafified balanced
tensor universality give equality. Apply I.representative on every cochain complex to
descend that equality through the exact computation counits. Paste the scalar cube;
the coefficient associators cancel by their unit-normalized section formulas.
The prescribed raw-localization component equation identifies the L component with
nativePullbackRationalComparison. Removing the endpoint equality yields the displayed
stage square. The argument is functorial for torsion and zero objects, allows E=L,
and never assumes inverse image commutes with arbitrary countable products. -/
theorem nativePullbackScalarCoherence (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (p : X ⟶ Y)
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (O : Operations l p R S) (I : ∀ E, IntegralComparison l p R S O E) :
    NativePullbackStageScalarCoherent l p R S O I := by sorry

end WeilConjectures.AdicQbarRealization.Proper
