/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X7
-/
module

public import Sheaf.Paper.FdIntegralScalarLiftProperty

/-! # Shifts and exactness of the integral scalar comparison

Source: trace-definition coefficient-category comparison, integral steps 1--6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.FdRawLocalization
namespace WeilConjectures

/-- A comparison fixed on good representatives by the actual completion map preserves
its prescribed shifts; its two endpoint composites are exact.
Source: trace-definition coefficient comparison, integral step 1, and the shift
normalization in lem-fd-normalized-integral-completion-comparison
(blueprint: lem-fd-integral-scalar-restriction-exact).

Proof: On a good K-flat representative the lift equation identifies b, after the
fully faithful coefficient inclusion, with ordinary coefficient transport followed
by the actual quotient-cocone completion map. The ordinary transport is uniquely
fixed on tensor generators by ordinary.generators. Its complex extension commutes
with signed reindexing. The normalized completion comparison has cone shift
(x,y) mapped to (x,(-1)^n y), fixing its (c(z),0) value, so the two maps have the
same shift square on these representatives. Every derived object admits a good
representative; naturality along the resolving isomorphism proves the square on
all objects. Insert integral_shift_normalization for the two supplied stage
functors and the normalization of the scalar shifts through their inclusions.
Faithfulness then gives the square for b with precisely the prescribed shifts.
The inverse square follows by cancelling b and its shift. Ordinary scalar
extension is exact for its adjunction-mate shift; the inclusion reflects
distinguished triangles. Together with hI this proves exactness of I followed by
C. Transfer distinguished triangles across b using its proved shift square to
obtain exactness of U followed by I. No inclusion is required to be strict.
-/
theorem fdIntegralScalarRestrictionExact
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (ordinary : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      FdOrdinaryScalarTransport l Ω T h)
    (b : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L)
    (hlift : fdIntegralScalarLiftProperty l Ω T stage ordinary b)
    (hI : ∀ E : Padic.FiniteCoefficientFields l Ω,
      (I l Ω T stage E).IsTriangulated) :
    (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      NatTrans.CommShift (b h).hom ℤ ∧ NatTrans.CommShift (b h).inv ℤ) ∧
    (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      (I l Ω T stage E ⋙ C l Ω T h).IsTriangulated ∧
        (U l Ω T h ⋙ I l Ω T stage L).IsTriangulated) := by sorry

end WeilConjectures
