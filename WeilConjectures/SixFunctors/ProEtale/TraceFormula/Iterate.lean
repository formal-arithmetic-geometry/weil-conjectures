/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Additivity

/-!
# Iterates of Weil complexes and the trace formula over a point

The `m`-th iterate of a Weil complex `(K, φ)` is the Weil complex `(K, φ_m)` with Frobenius
`Φ_m`; the trace formula in degree `m` for `(K, φ)` is the trace formula in degree one for its
`m`-th iterate. Over the base itself, `a_X = 𝟙 s`, the trace formula is a formal consequence of
the normalisations of the six-functor package at identities.

## Main definitions

- `AlgebraicGeometry.ProEtale.WeilComplex.iterate`: the `m`-th iterate `(K, φ_m)`.

## Main results

- `AlgebraicGeometry.ProEtale.WeilComplex.traceFormula_of_iterate`: the trace formula in degree
  `m` from the trace formula in degree one for the `m`-th iterate.
- `AlgebraicGeometry.ProEtale.WeilComplex.traceFormula_of_eq_id`: the trace formula over the
  base, `a_X = 𝟙 s`.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale.WeilComplex

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {s X : Scheme.{u}} {aX : X ⟶ s}

/-- The `m`-th iterate of a Weil complex `(K, φ)`: the Weil complex `(K, φ_m)` with Frobenius
`Φ_m` (part of blueprint `def-trf-frobenius-coefficient-morphism`). -/
noncomputable def iterate (W : WeilComplex (A := A) aX) (m : ℕ) : WeilComplex (A := A) aX where
  frobenius := W.frobeniusIterate m
  frobenius_comp := W.frobeniusIterate_comp m
  obj := W.obj
  coeff := W.coeffIterate m

variable [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- The trace formula in degree `m` for `(K, φ)` follows from the trace formula in degree one
for its `m`-th iterate `(K, φ_m)`: both are statements about the graph of `Φ_m` with coefficient
`φ_m`. -/
theorem traceFormula_of_iterate (G : GeometricOperations A s) [IsGeometric aX]
    [HasCompactification aX] (W : WeilComplex (A := A) aX) (hW : G.ctf X W.obj) (m : ℕ)
    [IsProper (W.graph G hW m).snd] [IsProper ((W.iterate m).graph G hW 1).snd]
    (h : (W.iterate m).TraceFormula G hW 1) : W.TraceFormula G hW m :=
  sorry

/-- The trace formula over the base: for a Weil complex on `a_X = 𝟙 s` the Frobenius is the
identity, the only fixed section is `𝟙 s`, and the global operator `F_{c,m}(φ)` on
`RΓ_c(s, K) ≃ K` is the stalk Frobenius `φ_m` at `𝟙 s`. -/
theorem traceFormula_of_eq_id (G : GeometricOperations A s) (W : WeilComplex (A := A) (𝟙 s))
    (hW : G.ctf s W.obj) (m : ℕ) [IsProper (W.graph G hW m).snd] : W.TraceFormula G hW m :=
  sorry

end AlgebraicGeometry.ProEtale.WeilComplex
