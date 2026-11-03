/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.RealSheaves.CohomologyEuler.RealSheavesCohomologyEulerSeries
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The three compact factors of a sheaf on a curve

Source: current blueprint, lem-wf-euler-product-middle-extension.proof.md,
first paragraph, via clause (3) of thm-trf-l-function-euler-product.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace RealSheaves.CohomologyEuler
open WeilConjectures

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
  [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

/-- Reverse characteristic polynomial of the canonical compact-support operator.
Source: d-real-cohom and the first proof paragraph of
lem-wf-euler-product-middle-extension
(blueprint: lem-wf-curve-sheaf-euler-identity). -/
def compactEulerFactor (hEll : ell ≠ D.p)
    (c : Compactification (D.geometricFiber X₀).hom) (K : Complex D ell X₀)
    (ι : PadicAlgCl ell →+* ℂ) (r : ℤ) : PowerSeries ℂ :=
  letI := (cohomology_finite D ell X₀ hEll c K).1 true r
  let A := frobeniusOnCohomology D ell X₀ hEll c K true r
  (((LinearMap.charpolyRev A.hom).map
    (ι.comp (ULift.ringEquiv : ULift.{u + 1} (PadicAlgCl ell) ≃+*
      PadicAlgCl ell).toRingHom) : Polynomial ℂ) : PowerSeries ℂ)

/-- The Euler series of any constructible Weil complex concentrated in degree zero
on a smooth curve has three compact factors.

Proof: apply clause (3) of thm-trf-l-function-euler-product to K. Smooth relative
dimension one bounds the dimension by one. Exact geometric-point sections commute
with homology, identifying the local cohomology of the derived stalk with the stalk
of each cohomology sheaf; the homology comparison is natural for the canonical
one-circuit Frobenius. Restriction along the canonical lifted-scalar equivalence
identifies the characteristic polynomials, after their stated embeddings in C.
Substitution T -> T^degree commutes with this coefficient map and with inverses of
constant-one series. Consequently the coefficientwise finite truncations agree with
eulerSeries. The same scalar restriction identifies the global compact operators.
Only cohomological degrees 0, 1 and 2 survive. Each reverse characteristic
polynomial has constant term one and is a unit. Multiply the trace formula's
quotient by the two even factors and use commutativity to obtain the identity.

This assertion does not assume affineness, connectedness, a dense open immersion,
or a lisse origin for the degree-zero sheaf.
Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
  sec-purity-real-sheaves/sec-weights-at-the-boundary-points/sk-p-real-semi/
  lem-wf-euler-product-middle-extension.proof.md, first paragraph,
  and thm-trf-l-function-euler-product, clauses (3) and (4)
(blueprint: lem-wf-curve-sheaf-euler-identity). -/
theorem curve_sheaf_euler_identity [SmoothOfRelativeDimension 1 X₀.hom]
    (hEll : ell ≠ D.p) (c : Compactification (D.geometricFiber X₀).hom)
    (K : Complex D ell X₀)
    (hK : ∀ r : ℤ, r ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj K.obj.carrier))
    (ι : PadicAlgCl ell →+* ℂ)
    (i : ∀ x : closedPoints X₀.left, X₀.left.residueField x.val →+* D.k)
    (hi : ∀ x, (i x).comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    eulerSeries D ell X₀ K ι i hi * compactEulerFactor D ell X₀ hEll c K ι 0 *
        compactEulerFactor D ell X₀ hEll c K ι 2 =
      compactEulerFactor D ell X₀ hEll c K ι 1 := by
  sorry

end RealSheaves.CohomologyEuler
