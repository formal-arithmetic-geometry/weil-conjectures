/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Paper.NormalizedCoefficientFamilies

/-! # Normalized completed-pullback families

Source: current blueprint, coefficient coherence of units, counits and mates.
(blueprint: lem-cbc-normalized-pull-family-existence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- The actual strict completed pullback has a normalized exact coefficient family.
This concerns one morphism, without compactification or exchange.

Source: current blueprint, coefficient coherence of units and counits;
lem-cbc-rational-compact-support-coefficient-coherence, steps 5, 11--13, 16.
(blueprint: lem-cbc-normalized-pull-family-existence).

Proof: a bounded integral input has uniformly bounded reductions, because each
uniformizer quotient has its two-term free resolution. Apply constructible
preservation to the square with proper vertical identities and horizontal g.
It gives preservation by the actual strict completed pullback, including the
uniform bounds and compatible etale origins. Derived reduction, tower pullback
and derived limit are exact and linear on the inherited triangulations.
Restrict and rationalize them. Construct the ambient scalar comparison from
ordinary balanced pullback and the scalar/completion reflector comparison.
Its completion-unit equation follows from the unit of the reflector. Transport
this comparison to the strict pullback via its unit-normalized comparison with
the reflector. The two ordinary transport maps give precisely the displayed
completionUnit equation of CbcCompletedPullCoefficientFamily. Reflection
uniqueness and the ordinary tensor associator give the successive-field law.
The tensor unit gives the repeated-field law. These equations and their shift
versions survive rationalization. Use the inverse comparison for beta, and
conjugate by the prescribed integral-scalar localization comparisons. Their
adjacent inverse pairs cancel, giving the specified beta equation and unit.
The functors are the localizations of the actual restrictions, so their
localization equality is literal. -/
theorem cbcCompletedPullCoefficientFamily_exists (g : Y ⟶ X) :
    Nonempty (CbcCompletedPullCoefficientFamily l Ω g) := by
  sorry

end AlgebraicGeometry.Scheme
