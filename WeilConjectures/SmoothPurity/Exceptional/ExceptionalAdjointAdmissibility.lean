/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.ConstructibleIntervalsUnordered
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.Algebra.Field.Shrink

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.SmoothPurity.Support.SupportScalarProjectionNormalization
import WeilConjectures.SmoothPurity.Exceptional.ExceptionalSupportProjectionIso
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension

/-!
# Exceptional-adjoint admissibility as optional ambient data

Source: Weil blueprint, order 1474 (blueprint: def-weil-exceptional-adjoint-admissibility).
Coefficient extension and the support comparison are constructed from scalar restriction.
Ambient exceptional adjoints, refinement coherence, preservation bounds, and invertibility
of the resulting right-adjoint coefficient mates are conditions of the datum.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

/-- The two preservation clauses for one actual ambient right adjoint, at fixed signed
bounds. Reversed output endpoints denote the zero subcategory through Set.Icc.
Source: Weil blueprint, order 1474, clauses (2) and (3)
(blueprint: def-weil-exceptional-adjoint-admissibility). -/
noncomputable def ExceptionalAdjointPreserves (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}}
    (G : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n) ⥤
      proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)) (cMinus cPlus : ℤ) :
    Prop :=
  (∀ (a b : ℤ), a ≤ b → ∀ L,
    constructibleInterval l E n hn Y a b L →
      constructibleInterval l E n hn X (a + cMinus) (b + cPlus) (G.obj L)) ∧
  ∀ L, finiteTorConstructible l E n hn Y L → finiteTorConstructible l E n hn X (G.obj L)

/-- Exceptional-adjoint admissibility at A_(E,n), relative to the chosen compactification.
FullCD is on all pro-etale module sheaves. The natural Hom bijections are adj; all
refinement coherence is datum, and the amplitude endpoints are independent signed integers.
Source: Weil blueprint, order 1474 (blueprint: def-weil-exceptional-adjoint-admissibility). -/
noncomputable def IsExceptionalAdjointAdmissibleAtFiniteStage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (_hS : ∀ s : S, IsUnit (l : S.presheaf.stalk s))
    [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
    (f : X ⟶ Y) [f.IsOver S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) : Prop :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  ∃ (D : SfAmbientExceptionalRightAdjointDatum (Padic.coefficientExtensionRing l E n) f c)
    (cMinus cPlus : ℤ), ExceptionalAdjointPreserves l E n hn (D.rightAdjoint c) cMinus cPlus

end WeilConjectures
