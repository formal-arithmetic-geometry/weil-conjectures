/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights

/-! # The specified local operator in a rank-one global basis

Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, dimension-zero
Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-weil-flags-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeilPointFlags

/-- The native local operator in a global rank-one Frobenius basis is scalar multiplication.
Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, dimension-zero
Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-weil-flags-scalar-comparison).

Proof: identify the residue degree with one and the chosen compatible lift with pointLift
using point_closed_geometry. The zero step of iterate is the given Weil structure.
Pull the global basis back along pointLift, compare pullback of its finite free target
with the rank-one free module, and identify that module with the regular module.
Applying pointSections and pointSectionsUnitIso gives a concrete linear equivalence e.
Naturality of pointComparison moves the global basis through the local-return composite.
At the regular module, upperStarIsoIdOfIsSepClosed_hom_app_unit identifies the Galois
trivialization with the inverse monoidal unit comparison. The unit coherence of
upperStarComp and upperStarCongr then identifies this composite with pullback of the
canonical upperStarFiniteFreeIso used in frobeniusMatrix. Thus the conjugated operator
is the restriction of the specified one-entry matrix map, not an arbitrary isomorphic
operator. Its value on 1 is ULift.up alpha by hmatrix and the definition of matrix.
Every linear map on the regular scalar module is multiplication by its value on 1,
so e intertwines the local operator with multiplication by ULift.up alpha. -/
theorem scalar_matrix_local_comparison (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p) (M : NativeL2.WeilModule D l (pointModel D))
    (alpha : (PadicAlgCl l)ˣ) (b : M.carrier ≅ free D l 1)
    (hmatrix : frobeniusMatrix D l M b = (fun _ _ ↦ (alpha : PadicAlgCl l)))
    (x : {x : (pointModel D).left // x ∈ closedPoints (pointModel D).left})
    (i : (pointModel D).left.residueField x.val →+* D.k)
    (hi : i.comp ((pointModel D).hom.residueFieldAlgebraMap x.val) =
      algebraMap D.k₀ D.k) :
    ∃ e : NativeCondensedModule.fibre l D M.carrier
        (NativeCondensedModule.localClosedPoint D (pointModel D) x i hi) ≃ₗ[
          ULift.{u + 1} (PadicAlgCl l)] ULift.{u + 1} (PadicAlgCl l),
      ∀ v, e ((NativeL2.closedOperator D l (pointModel D) M x i hi).hom v) =
        (ULift.up (alpha : PadicAlgCl l)) * e v := by sorry

end WeilConjectures.CondensedWeilPointFlags
