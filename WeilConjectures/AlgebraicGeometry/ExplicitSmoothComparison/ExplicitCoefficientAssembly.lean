/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExplicitSmoothComparison.ExplicitSmoothAdjunctionData

/-! # Finite and nonfinite parts of the explicit smooth adjunction

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-thm-purity-transport/sk-prop-sp-comparison-brown-explicit.proof.md,
finite paragraph, integral paragraph, rational/closure paragraph, and normalization.
(blueprint: def-pur-explicit-coefficient-assembly).

The finite family uses every finite commutative ell-primary coefficient ring.
Its predicates retain the literal DNC and affine normalization equations.
The assembly below selects only supplied adjunction data at each coefficient.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ExplicitSmoothComparison

local instance assemblySmallProEt (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _

/-- Finite adjunctions, including nonregular and zero rings.
Source: the finite paragraph (blueprint: def-pur-explicit-coefficient-assembly). -/
abbrev FiniteFamily (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] :=
  ∀ (A : CommRingCat.{0}) (fin : Finite A) (n : ℕ)
    (hA : (ell ^ (n + 1) : A) = 0) (s : Datum k),
    ExplicitAdjunction ell (.finite A fin n hA) s

/-- The finite coefficient cases of the published coefficient index.
Source: the finite paragraph (blueprint: def-pur-explicit-coefficient-assembly). -/
def IsFiniteCoefficient {ell : ℕ} [Fact ell.Prime] : Coefficient ell → Prop
  | .finite _ _ _ _ => True
  | _ => False

/-- Adjunctions at the integral, rational, and algebraic-closure coefficients.
Source: the three nonfinite paragraphs
(blueprint: def-pur-explicit-coefficient-assembly). -/
abbrev NonfiniteFamily (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] :=
  ∀ (c : Coefficient ell), ¬ IsFiniteCoefficient c →
    ∀ s : Datum k, ExplicitAdjunction ell c s

/-- Assemble supplied data coefficient by coefficient; no witness is chosen.
Source: the coefficient cases (blueprint: def-pur-explicit-coefficient-assembly). -/
def assemble {ell : ℕ} [Fact ell.Prime] {k : Type u} [Field k]
    (a : FiniteFamily ell k) (r : NonfiniteFamily ell k) : Family ell k :=
  fun c s ↦ match c with
  | .finite A fin n hA => a A fin n hA s
  | .integers => r .integers (by simp [IsFiniteCoefficient]) s
  | .rationals => r .rationals (by simp [IsFiniteCoefficient]) s
  | .integral E => r (.integral E) (by simp [IsFiniteCoefficient]) s
  | .rational E => r (.rational E) (by simp [IsFiniteCoefficient]) s
  | .closure => r .closure (by simp [IsFiniteCoefficient]) s

/-- Coherence between two finite coefficients through the specified scalar maps.
Source: finite normalization and reduction
(blueprint: def-pur-explicit-coefficient-assembly). -/
def FiniteFamily.scalarCompatible (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] (b : FiniteFamily ell k) : Prop :=
  ∀ (A : CommRingCat.{0}) (fin : Finite A) (n : ℕ) (hA : (ell ^ (n + 1) : A) = 0)
    (A' : CommRingCat.{0}) (fin' : Finite A') (n' : ℕ)
    (hA' : (ell ^ (n' + 1) : A') = 0),
    let c := Coefficient.finite A fin n hA
    let c' := Coefficient.finite A' fin' n' hA'
    ∀ a : c.bundled.{u} ell ⟶ c'.bundled ell,
    IsListedScalarCoefficientMap ell a →
    ∃ ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell,
    ∀ s : Datum k,
    ∃ p : ScalarLineCoordinates ell a ha s.X,
    ∀ K : c.ctf ell s.Y,
    ∃ hK : property ell c' s.Y ((scalarSixChange a s.Y).obj K.obj),
      (scalarSixChange a s.Y).map ((b A fin n hA s).trace K) =
        (scalarSupportMap a s.compactification).app
            ((c.smoothSource ell s.map s.dim).obj K.obj) ≫
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c'.obj ell) s.compactification).map
              (sourceScalar ell a s.map s.dim ha p K.obj) ≫
          (b A' fin' n' hA' s).trace ⟨_, hK⟩

/-- Scalar counit equations with at least one nonfinite coefficient.
Source: transported normalization
(blueprint: def-pur-explicit-coefficient-assembly). -/
def MixedScalarCompatible (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    (b : Family ell k) : Prop :=
  ∀ (c c' : Coefficient ell) (a : c.bundled.{u} ell ⟶ c'.bundled ell),
    IsListedScalarCoefficientMap ell a →
    (¬ IsFiniteCoefficient c ∨ ¬ IsFiniteCoefficient c') →
    ∃ ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell,
    ∀ s : Datum k,
    ∃ p : ScalarLineCoordinates ell a ha s.X,
    ∀ K : c.ctf ell s.Y,
    ∃ hK : property ell c' s.Y ((scalarSixChange a s.Y).obj K.obj),
      (scalarSixChange a s.Y).map ((b c s).trace K) =
        (scalarSupportMap a s.compactification).app
            ((c.smoothSource ell s.map s.dim).obj K.obj) ≫
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c'.obj ell) s.compactification).map
              (sourceScalar ell a s.map s.dim ha p K.obj) ≫
          (b c' s).trace ⟨_, hK⟩

end AlgebraicGeometry.ProEtale.ExplicitSmoothComparison
