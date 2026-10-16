/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients

/-! # Integral models on a locally finitely presented stratum

Source: Bhatt--Scholze, Lemmas 6.8.12--6.8.13 and Proposition 6.8.14(2).
(blueprint: lem-weil-pbc-continuous-constructible-integral-stratum)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

/-- A locally finitely presented rational module on one immersed stratum admits an
ordinary constructible integral model, with both coefficient rings pulled back from X.
Source: Hemo--Richarz--Scholbach, Example 3.1 (local triviality), and Bhatt--Scholze,
Lemma 6.8.13, with the coefficient restriction identification of Lemma 6.8.2.
(blueprint: lem-weil-pbc-continuous-constructible-integral-stratum)

Proof in words. An immersion identifies Y with a locally closed subspace of X, so Y
is topologically noetherian. Identify the two pulled-back coefficient rings and their
map with the continuous integral and rational coefficient rings on Y. A finite local
presentation over the rational ring is locally finite free: realize a presentation
matrix as continuous E-valued functions, refine by its locally constant rank, and use
an invertible maximal minor to identify its cokernel with a finite free module.
For this lisse module, the first paragraph of Lemma 6.8.13 gives lattices on a finite
refinement. More explicitly, Proposition 6.8.4(6) first gives lattices on an etale cover.
Take a finite affine subcover and stratify so its maps become finite etale. On each
connected resulting stratum, the lisse rational module comes from a continuous
representation of the profinite fundamental group: it does so on the finite etale
cover, and restriction to an open subgroup detects continuity of the representation.
Compactness gives an invariant integral lattice, by taking the sum of the translates
of one lattice; the translates lie between two fixed powers of a uniformizer times
that lattice, so this sum is still a finitely generated full lattice. Its associated
sheaf is locally finite free and hence has the finite presentations required here.
Apply the separate gluing theorem to these supplied models on the finite refinement,
and transport the result back across the coefficient identifications. For the zero
module and the empty stratum use zero. No derived comparison or bounded-complex
packaging is part of this statement. -/
theorem continuousConstructible_integral_stratum (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] {Y : Scheme.{u}} (i : Y ⟶ X) [IsImmersion i]
    (F : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      ((ProEtale.upperStar Ab.{u + 1} i).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X)))
    (hF : ProEtale.IsLocallyFinitelyPresented
      ((ProEtale.upperStar Ab.{u + 1} i).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X)) F) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        ((ProEtale.upperStar Ab.{u + 1} i).obj (condensedRingObj (integralCoeff ℓ E) X)),
      ProEtale.IsConstructibleModuleObject
        ((ProEtale.upperStar Ab.{u + 1} i).obj (condensedRingObj (integralCoeff ℓ E) X)) N ∧
      Nonempty ((Mod.extendScalars
        ((ProEtale.upperStar Ab.{u + 1} i).map
          (coefficientMap (integralScalarMap ℓ E) X))).obj N ≅ F) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
