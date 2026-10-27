/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.Paper.FiniteSmoothCoefficientArrows
public import Sheaf.SecSmoothPurity.DncCoefficientTransportData

/-! # Coefficient compatibility of the bundle zero-section integration adjunct

Source: blueprint/latest, smooth-purity reduction compatibility proof (3), Orientation,
and vector-bundle-purity proof, paragraph 2.
(blueprint: lem-sp-finite-bundle-section-adjoint-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The integration adjunct along a bundle zero section respects root-normalized
coefficient comparison, including a change from annihilator N to its divisor M.
Source: sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, (3), Orientation; sk-prop-an/
cor-pur-vector-bundle-purity.proof.md, paragraph 2.
(blueprint: lem-sp-finite-bundle-section-adjoint-scalar).

Proof: the power N/M on roots fits the Kummer sequence diagram whose map on the
first units sheaf is N/M and whose map on the second units sheaf is the identity.
It sends the N-boundary of O(1) to its M-boundary. The root-power and generator
conditions on t identify the induced balanced sheaf map with t.sheafIso. Its
derived normalization identifies the resulting derived map with t.derivedIso.
Consequently the normalized projective-line decomposition and its second-projection
trace satisfy the coefficient square, including the change of exponent. The
common-exponent scalar square is the vector trace scalar-descent theorem. Iterate
the projective-line and affine counits, using compact-support scalar composition
and its projection square at each step. The ordered tensor comparison is exactly
t.tensorPower d: multiplication on the coefficient unit at d=0, followed by the
specified tensor and shift comparisons at each successor. On bundle frames these
are the defining traces of vector integration; their open-restriction and refinement
coherences glue the scalar square. Transpose this trace square under the specified
compact-support/exceptional adjunctions. The integration-transpose scalar-mate
theorem identifies its exceptional map with the actual coefficient mate. Pull back
along the zero section and use scalar/pullback section cancellation to obtain the
stated square. Every tensor and scalar extension is derived, so B need not be flat
over A. At d=0 the empty tower and scalar unit give the equation. For N=M the root
power is the identity; on the empty base and for zero coefficients the maps are
unique. No deformation family or smooth orientation enters this argument. -/
theorem finiteBundleSectionAdjoint_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (hMN : M ∣ N)
    (hA : (N : A) = 0) (hB : (M : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S]
    (d : ℕ) (E : S.Modules) [E.IsFiniteLocallyFreeOfRank d]
    (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (M : Γ(S, ⊤)))
    (t : CoefficientLineComparison φ N M hA hB S) :
    letI := (vectorBundlePurityCompactification S d E).hasCompactification
    (ordinaryScalar φ S).map
        (FiniteRingSectionDeformation.bundleSectionAdjoint N hN A hA S hS d E) ≫
        WeilConjectures.DncCoefficientTransport.sectionMap φ
          (VectorBundleZeroSection.π S d E) (VectorBundleZeroSection.zero S d E) =
      (t.tensorPower d).hom ≫
        FiniteRingSectionDeformation.bundleSectionAdjoint M hM B hB S hS' d E := by sorry

end AlgebraicGeometry.Etale.FiniteSmoothPurity
