/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Pairing
public import WeilConjectures.EtaleCohomology.PoincareDuality.Setting

/-!

# The trace map and the trace–cup pairing

For a proper `X` the compactly supported and the ordinary cohomology agree, and the derived
Poincaré pairing takes the classical shape of a *trace–cup pairing*

`⟨x, y⟩_i = tr_X(x ⌣ y) : H^i(X, Λ) ⊗ H^{2d-i}(X, Λ) ⟶ Λ(-d)`,

where `tr_X : H^{2d}(X, Λ) ⟶ Λ(-d)` is the untwisted form of the counit of
`Ra_{X!} ⊣ Ra_X^!` read through the orientation. That `tr_X` is an isomorphism is the *trace
isomorphism*; the normalisation "the fundamental class goes to `1`" is then a choice of a
generator, not a further theorem.

## Main definitions and results

- `AlgebraicGeometry.ProEtale.traceMap`: the trace `tr_X : H^{2d}(X, Λ) ⟶ Λ(-d)`.
- `AlgebraicGeometry.ProEtale.traceCupPairing`: the trace–cup pairing `⟨-,-⟩_i`.
- `AlgebraicGeometry.ProEtale.isIso_traceMap`: the trace isomorphism.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

variable {X Y : Scheme.{u}}

/-- Blueprint `sk-def-trace-cup`: Trace and trace–cup pairing.

The trace `tr_X : H^{2d}(X, Λ) ⟶ Λ(-d)`, the untwisted form of the counit of
`Ra_{X!} ⊣ Ra_X^!` read through the orientation `γ`. -/
noncomputable def traceMap (a : X ⟶ Y) [HasCompactification a] (d : ℕ)
    (γ : ((tateTwist A X (d : ℤ)).obj (𝟙_ _))⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A a) :
    (cohomology A X (2 * d : ℤ)).obj (𝟙_ _) ⟶ twistedCoefficients A (-d : ℤ) :=
  sorry

/-- Blueprint `sk-def-trace-cup`: Trace and trace–cup pairing.

The trace–cup pairing `⟨x, y⟩_i = tr_X(x ⌣ y)`, a morphism
`H^i(X, Λ) ⊗ H^j(X, Λ) ⟶ Λ(-d)` in the coefficient category, for complementary degrees
`i + j = 2d`. -/
noncomputable def traceCupPairing (a : X ⟶ Y) [HasCompactification a] (d : ℕ)
    (γ : ((tateTwist A X (d : ℤ)).obj (𝟙_ _))⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A a)
    (i j : ℕ) (hij : i + j = 2 * d) :
    (cohomology A X (i : ℤ)).obj (𝟙_ _) ⊗ (cohomology A X (j : ℤ)).obj (𝟙_ _) ⟶
      twistedCoefficients A (-d : ℤ) :=
  sorry

end ProEtale

/-- Blueprint `sk-cor-trace`: The trace isomorphism.

For `X₀` in addition *proper*, the trace `tr_X : H^{2d}(X, Λ) ⟶ Λ(-d)` of the constant sheaf
is an isomorphism. It is the map produced by the duality at `i = 0`, so the normalisation
"the fundamental class goes to `1`" is a choice of generator of `H^{2d}(X, Λ) ≅ Λ(-d)`, not a
further statement. -/
theorem ProEtale.isIso_traceMap {k₀ : Type u} [Field k₀] [Finite k₀] {d : ℕ}
    (T : PoincareDualitySetting k₀ d) [IsProper T.modelStructureMorphism]
    (k : Type u) [Field k] [IsAlgClosed k] [Algebra k₀ k]
    [HasCompactification (T.structureMorphism k)]
    (γ : ((tateTwist A (T.geometricFibre k) (d : ℤ)).obj (𝟙_ _))⟦(2 * d : ℤ)⟧ ≅
      dualizingComplex A (T.structureMorphism k)) :
    IsIso (traceMap A (T.structureMorphism k) d γ) :=
  sorry

end AlgebraicGeometry
