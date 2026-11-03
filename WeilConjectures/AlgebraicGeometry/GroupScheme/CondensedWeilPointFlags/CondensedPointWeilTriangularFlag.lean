/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Realization of an invertible triangular matrix as a condensed Weil flag

Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, dimension-zero
Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-weil-flags-triangular-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeilPointFlags

/-- Leading triangular blocks give native Weil subobjects and their
actual rank-one cokernels, with their specified diagonal Frobenius scalars.
Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, dimension-zero
Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-weil-flags-triangular-realization).

Proof: let C be the matrix of A in basis, and let C_j be its leading j by j block.
Realize each C_j as a map of B^j using the scalar-normalized point sections: pullback
along pointLift is fully faithful, endomorphisms of the regular module are scalars by
pointSectionsUnit_bijective, and finite biproducts identify their maps with matrices.
The inverse matrix realizes the inverse map, so hblocks makes this an automorphism.
Precompose with the canonical Frobenius pullback comparison to give B^j its Weil
structure. The leading-coordinate inclusion and final-coordinate projection satisfy
C_(j+1) I_j = I_j C_j and pi_j C_(j+1) = C(j,j) pi_j, by upper triangularity.
The canonical comparison is natural for these constant matrices, so both maps are
Weil-equivariant. Inclusion has a coordinate retraction as a module map and hence is
monic among Weil maps. Projection is the module cokernel. A module factor through it
is equivariant because its two equivariance composites agree after precomposing with
the Frobenius pullback of projection, which is split epic. Uniqueness is inherited
from module maps. Therefore the Weil cokernel is the rank-one module with diagonal
scalar C(j,j); choose its unit from hdiag and transport its basis across this unique
cokernel isomorphism. The zero-rank
finite biproduct is zero, also in the Weil category. Finally the basis isomorphism P
and e give a Weil isomorphism B^d to M because AP = PC. This realizes the actual
subobjects and cokernels without a diagonalizability assumption. -/
theorem triangular_basis_flag (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p) (M : NativeL2.WeilModule D l (pointModel D)) (d : ℕ)
    (e : M.carrier ≅ free D l d)
    (A : (Fin d → PadicAlgCl l) ≃ₗ[PadicAlgCl l] (Fin d → PadicAlgCl l))
    (_hA : A.toLinearMap = (frobeniusMatrix D l M e).mulVecLin)
    (basis : Module.Basis (Fin d) (PadicAlgCl l) (Fin d → PadicAlgCl l))
    (hupper : (LinearMap.toMatrix basis basis A.toLinearMap).IsUpperTriangular)
    (hdiag : ∀ j, IsUnit (LinearMap.toMatrix basis basis A.toLinearMap j j))
    (hblocks : ∀ (j : ℕ) (hj : j ≤ d), IsUnit
      ((LinearMap.toMatrix basis basis A.toLinearMap).submatrix (Fin.castLE hj)
        (Fin.castLE hj)))
    (hblockeq : ∀ j : Fin d,
      let C := LinearMap.toMatrix basis basis A.toLinearMap
      let Cj := C.submatrix (Fin.castLE (Nat.le_of_lt j.isLt))
        (Fin.castLE (Nat.le_of_lt j.isLt))
      let Cj1 := C.submatrix (Fin.castLE (Nat.succ_le_of_lt j.isLt))
        (Fin.castLE (Nat.succ_le_of_lt j.isLt))
      let I : Matrix (Fin (j.val + 1)) (Fin j.val) (PadicAlgCl l) :=
        fun r k ↦ if r = k.castSucc then 1 else 0
      let π : Matrix (Fin 1) (Fin (j.val + 1)) (PadicAlgCl l) :=
        fun _ k ↦ if k = Fin.last j.val then 1 else 0
      Cj1 * I = I * Cj ∧ π * Cj1 = C j j • π)
    (hcoordsplit : ∀ n : ℕ,
      let I : Matrix (Fin (n + 1)) (Fin n) (PadicAlgCl l) :=
        fun r k ↦ if r = k.castSucc then 1 else 0
      let R : Matrix (Fin n) (Fin (n + 1)) (PadicAlgCl l) := I.transpose
      let P : Matrix (Fin 1) (Fin (n + 1)) (PadicAlgCl l) :=
        fun _ k ↦ if k = Fin.last n then 1 else 0
      let S : Matrix (Fin (n + 1)) (Fin 1) (PadicAlgCl l) := P.transpose
      R * I = 1 ∧ P * S = 1 ∧ P * I = 0 ∧ I * R + S * P = 1)
    (blockWeil : ∀ (j : ℕ) (hj : j ≤ d),
      ∃ (N : NativeL2.WeilModule D l (pointModel D)) (b : N.carrier ≅ free D l j),
        frobeniusMatrix D l N b = (LinearMap.toMatrix basis basis A.toLinearMap).submatrix
          (Fin.castLE hj) (Fin.castLE hj))
    (matrix_bijective : ∀ a b : ℕ, Function.Bijective (matrix D l (a := a) (b := b)))
    (matrix_comp : ∀ (a b c : ℕ) (f : free D l a ⟶ free D l b)
      (g : free D l b ⟶ free D l c), matrix D l (f ≫ g) = matrix D l g * matrix D l f)
    (matrix_id : ∀ a : ℕ, matrix D l (𝟙 (free D l a)) = 1)
    (pullback_fixed : ∀ (a b : ℕ) (f : free D l a ⟶ free D l b),
      CondensedRing.upperStarFinFreeMap (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius (pointModel D)).hom f = f) :
    ∃ (G : Fin (d + 1) → NativeL2.WeilModule D l (pointModel D))
      (f : ∀ j : Fin d, G j.castSucc ⟶ G j.succ),
      IsZero (G 0) ∧ Nonempty (G (Fin.last d) ≅ M) ∧
      (∀ j, Nonempty ((G j).carrier ≅ free D l j.val)) ∧
      (∀ j : Fin d, Mono (f j)) ∧
      ∀ j : Fin d,
        ∃ (alpha : (PadicAlgCl l)ˣ)
          (b : (cokernel (f j)).carrier ≅ free D l 1),
          (alpha : PadicAlgCl l) = LinearMap.toMatrix basis basis A.toLinearMap j j ∧
          frobeniusMatrix D l (cokernel (f j)) b =
            (fun _ _ ↦ (alpha : PadicAlgCl l)) := by sorry

end WeilConjectures.CondensedWeilPointFlags
