module

public import Sheaf.Paper.IteratedReturnTransportData

/-! # Scalar compatibility of the two return words

Source: blueprint trace-transport, local normalization Steps 3
(blueprint: lem-trf-return-scalar-squares).
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

/-- The return comparison commutes with scalar change on the whole quotient diagram,
and on its integral and raw rational realizations.
Source: the scalar-calculus node's proof Step 3, local normalization Step 9
(blueprint: lem-trf-return-scalar-squares).

Proof: let H be pullback along the common composite scheme map. Write r_E and s_E
for its two normalized comparisons to U_E^m P_E and P_E G_E^m, and similarly over M.
Induct on the word length using systemScalarComposition and scalarComposition of hC.
At length one these are exactly their mixed comparison squares. At the next step,
use naturality of the one-step scalar comparison at the preceding power compositor,
then the induction hypothesis. Equality of the composite scheme maps identifies their
scalar comparison b. This gives r_M b = U_M^m(a) delta T_s(r_E) and
s_M b = P_M(d) a T_s(s_E), already on entire diagrams. Substitute v=s r inverse,
compose the first equality with s_M r_M inverse, and cancel T_s(r_E). The second
equality gives the asserted return identity. Realization preserves composition,
inverses and equality. Finally apply raw rationalization; its object identifications
conjugate the same diagram and its Hom tensor products preserve this equality.
No perfectness, Tor-amplitude or idempotent-completion assumption enters. -/
theorem returnScalarSquares
    (hC : IntegralComparisonRealizationCoherence l E M ι C)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x)]
    [∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x)]
    (r : ℕ) (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1))) :
    SystemScalarEquation D l E X₀ M ι r z w ∧
      IntegralScalarEquation D l E X₀ C M ι r z w ∧
      RationalScalarEquation D l E X₀ C M ι r z w := by sorry

end WeilConjectures
