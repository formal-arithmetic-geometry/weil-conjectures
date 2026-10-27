module

public import Sheaf.Paper.IteratedReturnTransportData

/-! # Unit and tower laws for the one-step raw rational pullback comparison

Source: blueprint trace-transport, local normalization Steps 6
(blueprint: lem-trf-rational-scalar-single-step-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open IteratedReturnTransport

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (C : IntegralComparisonSystem.{u} l)
  (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (ι : E →ₐ[ℚ_[l]] M)
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (j : M →ₐ[ℚ_[l]] L)

/-- Raw rationalization preserves the normalized unit and tensor tower square for
one pullback. The iterated normalization will follow by categorical induction.
Source: the scalar-calculus node's proof Step 6, local normalization Steps 8--9
(blueprint: lem-trf-rational-scalar-single-step-normalization).

Proof: use scalarIdentity and scalarTower of hC for the specified integral comparison.
Apply the raw localization functor, which preserves composition and maps inverses
to inverses. The object formula of rationalDerivedPullback and that of
sfRationalScalarExtension identify the source and target with the prescribed
rational objects. Under these identifications the localized comparison is precisely
integralComparisonRationalScalarComponent. The uniquely normalized
sfRationalScalarUnit and sfRationalScalarComp are the localizations of the integral
multiplication unit and completion-conjugated tensor associator. Substitute these
formulas into the two localized equations and cancel each adjacent object
identification with its inverse. This gives the unit and tower identities at
length one. All arguments use the full constructible integral domain, without
finite Tor-amplitude, and its raw rationalization. -/
theorem rationalScalarSingleStepNormalization
    (hC : IntegralComparisonRealizationCoherence l E M ι C)
    (Y : Scheme.{u}) [∀ y : Y, Invertible (l : Y.residueField y)] (g : Y ⟶ Y) :
    RationalPowerNormalization l E C M ι L j Y g 1 := by sorry

end WeilConjectures
