/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedWeilPointFlags.CondensedPointWeilScalarComparison

/-! # Scalar local spectrum on a rank-one native Weil module

Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, dimension-zero
Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-weil-flags-scalar-spectrum).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeilPointFlags

/-- The scalar of a rank-one Frobenius matrix is its only native local eigenvalue.
Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, dimension-zero
Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-weil-flags-scalar-spectrum).

Proof: point_closed_geometry identifies every compatible geometric lift with pointLift
and its residue degree with one. Unfolding the zero step of the positive-power Weil
iteration leaves the original structure isomorphism. Pull the given basis back to this
point and use the canonical finite-free pullback comparison. Naturality of the point
comparison transports the basis across the local return. On the regular module its
normalization is the inverse monoidal unit comparison, by
CondensedRing.upperStarIsoIdOfIsSepClosed_hom_app_unit; on its finite powers it is the
biproduct of these comparisons. Thus the local operator in this pulled-back basis is
exactly the one-entry matrix specified by hmatrix. The scalar-normalized unit-section
isomorphism identifies its action on sections with multiplication by ULift.up alpha.
For a nonzero eigenvector v with eigenvalue beta, the two formulas for its image give
(beta - ULift.up alpha) smul v = 0. A vector space over a field has no zero divisors
in scalar multiplication, so beta = ULift.up alpha; taking down gives the assertion.
This compares the specified operators, rather than merely their isomorphism classes,
and is independent of both the residue embedding and a complex coefficient embedding. -/
theorem scalar_matrix_local_eigenvalue (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p) (M : NativeL2.WeilModule D l (pointModel D))
    (alpha : (PadicAlgCl l)ˣ) (b : M.carrier ≅ free D l 1)
    (hmatrix : frobeniusMatrix D l M b = (fun _ _ ↦ (alpha : PadicAlgCl l)))
    (x : {x : (pointModel D).left // x ∈ closedPoints (pointModel D).left})
    (i : (pointModel D).left.residueField x.val →+* D.k)
    (hi : i.comp ((pointModel D).hom.residueFieldAlgebraMap x.val) =
      algebraMap D.k₀ D.k)
    (beta : ULift.{u + 1} (PadicAlgCl l))
    (hbeta : Module.End.HasEigenvalue
      (NativeL2.closedOperator D l (pointModel D) M x i hi).hom beta) :
    beta.down = (alpha : PadicAlgCl l) := by
  obtain ⟨e, he⟩ := scalar_matrix_local_comparison D l _hl M alpha b hmatrix x i hi
  obtain ⟨v, hv⟩ := hbeta.exists_hasEigenvector
  have h := congrArg e hv.apply_eq_smul
  rw [he, e.map_smul] at h
  have hev : e v ≠ 0 := by
    intro hz
    exact hv.2 (e.injective (hz.trans e.map_zero.symm))
  have hscalar : (ULift.up (alpha : PadicAlgCl l)) = beta :=
    mul_right_cancel₀ hev h
  exact (congrArg ULift.down hscalar).symm

end WeilConjectures.CondensedWeilPointFlags
