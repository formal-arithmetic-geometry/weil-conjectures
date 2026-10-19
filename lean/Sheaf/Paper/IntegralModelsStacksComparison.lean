/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Paper.IntegralModelsDefinitions

/-! # Stacks criterion for embedded integral coefficients

Source: blueprint main-20261015, sk-lem-integral-models, proof step 3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The Stacks constructibility criterion transported to the embedded coefficient model.

Source: blueprint main-20261015, sk-lem-integral-models, proof step 3, and
sk-lem-integral-models-stacks, Stacks 09C1.
(blueprint: lem-sfb-embedded-integral-stacks-comparison).

Proof: first lift the embedded field to ULift in the scheme universe, since the published
Stacks theorem binds the field and scheme in the same universe. Uniqueness of the extending
absolute value identifies the embedded integer ring with Padic.coefficientExtensionIntegers.
Transport constant and continuous rings along this scalar ring isomorphism. Constant
sheafification, continuous functions, and inverse image preserve this isomorphism and its
canonical constant-to-continuous map. The two uniformizers generate
the maximal ideal, hence the first residue quotients and their reduction maps agree after
coefficient transport. Exact restriction and derived extension of scalars commute with these
isomorphisms, as checked on K-flat representatives. The section-action and small-site
identifications preserve the quotient-kernel completeness predicate, constructible cohomology,
and every relative Tor interval. Apply IntegralModelsStacks.integral_models_stacks to the
lifted field, and substitute these identifications into its first clause. No ambient
equivalence between constant and completed coefficients is asserted. Empty strata and the
zero object require no change to any construction. -/
theorem embeddedIntegral_stacks_comparison
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (integralCoefficientObject X ℓ E))) :
    constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X K ↔
      IntegralModelsEmbedded.stacksConstructible ℓ E π X
        ((IntegralModelsEmbedded.restriction ℓ E X).obj K) := by sorry

end AlgebraicGeometry.ProEtale
