/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.RealPurityNativeExteriorDefs

/-! # The Rankin estimate on actual native Weil modules

Source: sk-p-real-rankin and sk-p-real-purity, exterior-power estimate
(blueprint: lem-rp-native-rankin-bound).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2
open NativeCondensedModule

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The analytic Rankin bound, expressed on the actual native local operators.
Source: sk-p-real-rankin and sk-p-real-purity, second and third paragraphs
(blueprint: lem-rp-native-rankin-bound).

Proof: first work on an affine smooth geometrically connected curve. Replace M by its
semisimplification, preserving local characteristic polynomials and constituent weights.
Its restriction to geometric monodromy is semisimple. For m >= 1 put T=M^(tensor 2m).
Every constituent of T has determinant weight at most 2m*d. The top-cohomology formula
identifies H_c^2(T) with the geometric coinvariants, twisted by (-1). Their simple Weil
factors are one-dimensional, with eigenvalues b satisfying 2*log_q|iota(b)| <= 2m*d.
Thus the eigenvalues of H_c^2(T) have norm at most q^(m*d+1). Affine H_c^0 vanishes,
and the trace formula expresses L(T,t) as the H_c^1 determinant divided by the H_c^2
determinant. This rational function is holomorphic on |t| < q^(-m*d-1). Positivity for
even tensor powers of a real module forces every local determinant to have no zero
on that disc. Since alpha^(2m) occurs on T at x, the roots of
1-iota(alpha)^(2m)*t^(degree x) have modulus at least q^(-m*d-1). Therefore
|iota(alpha)|^2 <= q_x^(d+1/m). Let m tend to infinity to get q_x^d. For an arbitrary
curve, restrict to an affine neighbourhood of the chosen closed point. The normal
connected curve has surjective geometric and arithmetic fundamental-group maps on
this nonempty open, hence a surjective Weil-group map preserving degrees. Its simple
constituents therefore remain exactly the restricted simple constituents, with the
same determinant weights; reality and local Frobenius at x are unchanged. Apply the
affine estimate there. -/
theorem native_rankin_bound
    [IsSeparated X₀.hom] [SmoothOfRelativeDimension 1 X₀.hom]
    [GeometricallyConnected X₀.hom]
    (hl : l ≠ D.p) (M : WeilModule D l X₀) (iota : PadicAlgCl l →+* ℂ) (d : ℝ)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (hreal : NativeCondensedWeil.Real D l X₀ M iota) (hne : ¬ IsZero M)
    (hd : ConstituentDeterminantBound D l X₀ M iota d)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (α : ULift.{u + 1} (PadicAlgCl l))
    (hα : Module.End.HasEigenvalue (closedOperator D l X₀ M x i hi).hom α) :
    ‖iota α.down‖ ^ 2 ≤ (Nat.card (X₀.left.residueField x.val) : ℝ) ^ d := by sorry

end WeilConjectures.NativeL2
