/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.Paper.CompletedExtensionZeroComparison
public import Sheaf.Paper.CompletedPullback
public import Sheaf.Paper.RingedEtaleOriginWitness

/-!
# Finite etale origins after completed-coefficient open extension

Source: blueprint thm-cbc-complete-proetale, proof step 2; Stacks 03DI, 09AF and 0GL1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Open extension preserves an independently retained bounded-below etale origin at
each positive quotient. Neither completeness nor a common bound is required.

Source: blueprint thm-cbc-complete-proetale, proof step 2; Stacks 03DI, 09AF and 0GL1
(blueprint: lem-cbc-completed-open-finite-etale-origins).
Proof: fix n and put B = A/I^(n+1). Choose a flat-term K-flat representative of K.
The coefficient-linear tensor/open comparison identifies reduction of its completed
open extension with extension of its B-reduction. The map sends [x] tensor b to
[x tensor b restricted to the open]. It is B-linear before any scalar restriction.
The finite constants-to-functions isomorphism transports this map to constant
B-coefficients, where extension is the usual exact pro-etale extension by zero.
Extend the retained etale antecedent by the exact etale extension by zero. The
etale/pro-etale open comparison identifies its realization with extension of the
original realization. Compose that comparison, extension of the retained origin
isomorphism, and the inverse tensor/open identification. Exact etale extension
preserves the particular antecedent's lower cohomological bound, giving the required
FiniteEtaleOriginWitness. Do this independently for every n. The empty open gives
the zero object, and for the zero quotient ring all module categories are zero;
the same tensor and section formulas apply in both cases. -/
theorem cbcCompletedOpenFiniteEtaleOrigins
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : d.derived U)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness U (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction U n).obj K)) :
    Nonempty (∀ n : ℕ, FiniteEtaleOriginWitness T (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction T n).obj ((cbcDerivedOpenShriek d j inferInstance).obj K))) := by
  sorry

end AlgebraicGeometry.Scheme
