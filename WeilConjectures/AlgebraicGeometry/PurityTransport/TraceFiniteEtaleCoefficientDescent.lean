/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.NativeFiniteEtaleDerivedTrace

/-! # Descent of the finite-etale counit identity through coefficients -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- The rank-zero trace equality descends from finite coefficients to the remaining
admissible condensed coefficients for the same scalar-compatible family.
Source: smooth trace clause (3), integral counit reconstruction and scalar passage.
(blueprint: new-det-sp-trace-finite-etale-coefficient-descent).

Proof in words. For integral coefficients apply positive finite quotient scalar
change to the two maps in the claimed equality. ScalarCompatible identifies the
first with the given finite-coefficient trace. Finite direct image is computed by
finite products, so scalar change commutes with it and carries the descended
sheet trace to the descended finite sheet trace. The source, zero-line and
proper/open comparisons satisfy their defining scalar squares; thus the finite
hypothesis identifies the two reduced maps. Reconstruct the integral target by
its canonical reduction tower. For constructible finite-Tor sources on this
finite-type base, the shifted finite-reduction Hom groups are finite. The Milnor
injection therefore makes equality of all reductions imply equality of the
integral maps; no unconditional faithfulness of derived evaluation is used.
Localize integral models for rational coefficients, using the same scalar counit
square. Every rational constructible finite-Tor object has such a model after
clearing denominators, so the equality holds for it. For the algebraic closure
choose one common finite extension for the object and all arrows and then apply
the finite-stage equality. Independence of stage follows from the listed scalar
maps. The conclusion concerns precisely the five non-finite cases. Empty
schemes and zero objects are included throughout. -/
theorem traceFiniteEtale_coefficientDescent
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (a : AdjunctionFamily ell D) (hS : ScalarCompatible ell D a)
    (hfinite : ∀ (A : CommRingCat.{0}) (fin : Finite A) (n : ℕ)
      (hann : (ell ^ (n + 1) : A) = 0),
      TraceFiniteEtaleSheetEquation ell D a (.finite A fin n hann)) :
    TraceFiniteEtaleSheetEquation ell D a .integers ∧
      TraceFiniteEtaleSheetEquation ell D a .rationals ∧
      (∀ E : PadicAlgCl.FiniteIntermediateField ell,
        TraceFiniteEtaleSheetEquation ell D a (.integral E) ∧
          TraceFiniteEtaleSheetEquation ell D a (.rational E)) ∧
      TraceFiniteEtaleSheetEquation ell D a .closure := by
  sorry

end AlgebraicGeometry.ProEtale.PurityTransport
