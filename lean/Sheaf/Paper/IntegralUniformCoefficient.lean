/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.PbcRationalCategory
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite-extension specialization and scalars for the published complete category

Source: Weil blueprint, proper base change, order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete).
The category is the published PbcIsBoundedConstructibleComplete, specialized to the
actual unlifted valuation ring in Type (u+1). Its completion, uniform reductions and
compatible origins are reused without redefining them. The published finite-extension
convenience abbreviation instead takes E in Type u and lifts its valuation ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The finite-extension valuation ring has the coefficient properties required by
this definition. Source: blueprint order 1300; Serre, Local Fields, Chapter II, §2
(blueprint: def-weil-pbc-bounded-constructible-complete).
Proof: the recorded valuation ring is a DVR with finite residue field. Its uniformizer
is nonzero and generates the maximal ideal. The ideal is principal and the ring is
Noetherian. The positive quotients are finite and have the length-one finite free
resolution given by multiplication by the corresponding uniformizer power; hence they
are perfect. The first quotient is a finite field of characteristic l, so it is torsion. -/
theorem pbcPadicCoefficientFacts (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    IsNoetherianRing (Padic.coefficientExtensionIntegers l E) ∧
      (Ideal.span {Padic.coefficientExtensionUniformizer l E}).FG ∧
      (∀ x : Padic.coefficientExtensionIntegers l E ⧸
          Ideal.span {Padic.coefficientExtensionUniformizer l E},
        ∃ m : ℕ, 0 < m ∧ m • x = 0) ∧
      (∀ n : ℕ, Finite (Padic.coefficientExtensionRing l E (n + 1))) ∧
      (∀ n : ℕ, 1 ≤ n → adicQuotientPerfect (Padic.coefficientExtensionIntegers l E)
        (Ideal.span {Padic.coefficientExtensionUniformizer l E}) n) := by
  sorry

/-- The actual p-adic coefficient datum, with its principal ideal and positive quotients.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcPadicCoefficientDatum (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E) where
  ideal := Ideal.span {Padic.coefficientExtensionUniformizer l E}
  noetherian := (pbcPadicCoefficientFacts l E).1
  finitelyGenerated := (pbcPadicCoefficientFacts l E).2.1
  quotientTorsion := (pbcPadicCoefficientFacts l E).2.2.1
  quotientFinite := (pbcPadicCoefficientFacts l E).2.2.2.1
  quotientPerfect := (pbcPadicCoefficientFacts l E).2.2.2.2

variable (T : Scheme.{u})

/-- Specialize the published three-clause predicate to the actual valuation ring.
Its coefficient and site universes are independent of the smaller convenience wrapper.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev IsPbcBoundedConstructibleComplete (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  PbcIsBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E)

/-- The published full subcategory specialized to the actual finite-extension integers.
The base hypotheses are exactly those of the integral category in the source.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev pbcBoundedConstructibleComplete (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [IsNoetherian T] (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (_hl : IsUnit (l : Γ(T, ⊤))) :=
  PbcBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E)

end AlgebraicGeometry.Scheme
