/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicStrictRealizationComparison
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransitionUnique
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsTensorTransition
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarComponentUnderlying

/-! # The scalar realization of the strict quotient coordinates

Source: Stacks Project, Tags 03CY, 03DA, 03EK and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

section Realization

variable (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
  (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
    completedAdicFiniteCommRing X d n)
  (hcompat : FinitePerfectModelsCompatible X d φ)
  (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt) (f : W ⟶ finitePerfectAdicChartObject V U)

end Realization

end AlgebraicGeometry.Scheme
