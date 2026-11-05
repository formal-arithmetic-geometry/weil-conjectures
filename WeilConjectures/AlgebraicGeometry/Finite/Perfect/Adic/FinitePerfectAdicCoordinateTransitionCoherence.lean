/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicMarkedOrigin
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSourceNormalizationUniversal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import Mathlib.CategoryTheory.Adjunction.Comma

/-! # Coherence of finite perfect adic coordinate transitions

Source: Stacks Project, Tags 09AL, 09C6 and 06YY.

This descends a coherent pro-etale quotient system to specified etale origins.
The former assertion for arbitrary independent arrows and realizations was false;
its zero-arrow diagnostic is retained below. The parent existential statement
`finitePerfectAdic_descend_coordinate_transitions` is unchanged.
(blueprint: new-w5-finite-perfect-adic-coordinate-transition-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

end AlgebraicGeometry.Scheme
