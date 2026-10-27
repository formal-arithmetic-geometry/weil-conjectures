module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import WeilConjectures.LinearAlgebra.Matrix.CauchyBinet
import Mathlib.RingTheory.Localization.Defs
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Faithful regular matrices of a finite group scheme

Source: Milne, Algebraic Groups (2017), Theorem 4.9, printed p.87, and the proof of
Proposition 11.32, printed p.221.
(blueprint: lem-sfb-finite-group-faithful-regular-matrices)

The coordinate algebra is the actual global-section Hopf algebra. Its comultiplication
fixes the right-translation convention. Matrices express the intrinsic automorphisms of
its scalar extensions in a basis; no reducedness or commutativity of the group is assumed.
-/

@[expose] public section

universe u

open CategoryTheory

set_option autoImplicit false
open scoped TensorProduct MonObj

namespace AlgebraicGeometry

/-- The right regular representation is a closed immersion, with surjective coordinate map,
identity evaluation, and its specified action on every algebra-valued point.

Source: Milne, Algebraic Groups (2017), Remark 4.1, printed p.84; Theorem 4.9, printed p.87;
Proposition 11.32, printed p.221.
(blueprint: lem-sfb-finite-group-faithful-regular-matrices)

Proof plan:
1. Finiteness makes the global-section algebra finite-dimensional. Its Hopf structure is
   `lem-sfb-affine-group-coordinate-hopf`. Choose a basis and expand its coproduct to get U.
   Coordinate functionals extract the coefficients uniquely, also after scalar extension
   (`def-weil-vector-space-dimension`, `def-weil-pbc-module-tensor-product`).
2. Coassociativity gives Delta(u_ij) = sum_r u_ir tensor u_rj. The right counit identity
   gives epsilon(u_ij) = delta_ij (`lem-sfb-affine-group-coordinate-hopf`).
3. On A tensor R the formula in the conclusion is (id tensor x)Delta, extended R-linearly.
   The coproduct identity gives multiplication of matrices, and the antipode gives a
   two-sided inverse. All these formulas commute with algebra homomorphisms R to R'.
4. At the universal point the matrix is invertible. Square Cauchy--Binet
   (`lem-weil-pbc-cauchy-binet`, `def-weil-pbc-matrix-determinant`) makes its determinant
   a unit. Evaluate the polynomial variables and extend to the localization
   (`def-weil-pbc-mv-polynomial-ring`, `lem-weil-pbc-ring-localization-universal-property`).
   Spec of this map gives rho (`def-sc-general-linear-group`, `def-weil-affine-spectrum`).
   The coefficient identities imply the group diagrams on the generators, hence on the
   localization; use `lem-weil-pbc-fibre-product-affine-spectra` for the product diagram.
5. The left counit identity gives b_j = sum_i epsilon(b_i)u_ij. Thus every basis vector,
   and hence every element of A, is in the image of the coordinate map, proving surjectivity.
6. Apply `lem-weil-pbc-closed-immersion-affine-cover-criterion` to the whole affine target.
   Evaluating the tensor formula at z gives a(zx), so these are right translations.
   Changing basis conjugates the same intrinsic operators on A tensor R.
-/
def FiniteGroupRegularMatrices
    (k : CommRingCat.{u}) (G : Scheme.{u}) [G.Over (Spec k)]
    [GrpObj (G.asOver (Spec k))] (hG : IsAffine G) : Prop :=
    letI := hG
    letI := GeneralLinearGroup.instGrpObjOverSchemeSpecOf
      (LinearGroupSchemes.Index.{u} (Module.finrank k Γ(G, ⊤))) k
    ∃ (b : Module.Basis (LinearGroupSchemes.Index.{u} (Module.finrank k Γ(G, ⊤)))
        k Γ(G, ⊤))
      (ρ : G.asOver (Spec k) ⟶ GeneralLinearGroup
        (LinearGroupSchemes.Index.{u} (Module.finrank k Γ(G, ⊤))) k)
      (U : Matrix (LinearGroupSchemes.Index.{u} (Module.finrank k Γ(G, ⊤)))
        (LinearGroupSchemes.Index.{u} (Module.finrank k Γ(G, ⊤))) Γ(G, ⊤))
      (φ : Matrix.GeneralLinearGroup.CoordinateRing
        (LinearGroupSchemes.Index.{u} (Module.finrank k Γ(G, ⊤))) k →ₐ[k] Γ(G, ⊤)),
      IsMonHom ρ ∧ IsClosedImmersion ρ.left ∧ Function.Surjective φ ∧
      ρ.left = G.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ∧
      (∀ i j, φ (Matrix.GeneralLinearGroup.coord _ k i j) = U i j) ∧
      (∀ j, Coalgebra.comul (R := k) (b j) = ∑ i, b i ⊗ₜ[k] U i j) ∧
      (∀ i j, Coalgebra.counit (R := k) (U i j) = if i = j then 1 else 0) ∧
      ∀ (R : Type u) [CommRing R] [Algebra k R],
        ∃ t : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ G.asOver (Spec k)) →*
            @LinearEquiv R R _ _ (RingHom.id R) (RingHom.id R) _ _
              (Γ(G, ⊤) ⊗[k] R) (Γ(G, ⊤) ⊗[k] R) _ _
              (Algebra.TensorProduct.rightAlgebra (R := k) (A := Γ(G, ⊤))).toModule
              (Algebra.TensorProduct.rightAlgebra (R := k) (A := Γ(G, ⊤))).toModule,
          (∀ x i j,
            (GeneralLinearGroup.homMulEquiv _ k R (x ≫ ρ) : Matrix _ _ R) i j =
              (Spec.preimage (x.left ≫ G.isoSpec.hom)).hom (U i j)) ∧
          (∀ x j r, t x (b j ⊗ₜ[k] r) =
            ∑ i, b i ⊗ₜ[k] ((Spec.preimage (x.left ≫ G.isoSpec.hom)).hom (U i j) * r)) ∧
          (∀ x y, GeneralLinearGroup.homMulEquiv _ k R ((x * y) ≫ ρ) =
            GeneralLinearGroup.homMulEquiv _ k R (x ≫ ρ) *
              GeneralLinearGroup.homMulEquiv _ k R (y ≫ ρ))

/-- A finite group scheme has the regular matrices and closed immersion specified above.
Source: Milne, Algebraic Groups (2017), Theorem 4.9, printed p.87, with V = A, as in
Proposition 11.32, printed p.221.
(blueprint: lem-sfb-finite-group-faithful-regular-matrices)

Proof: use the six steps in `FiniteGroupRegularMatrices`: expand the coproduct in a basis,
apply coassociativity and both counit identities, invert using the antipode, evaluate the
localized polynomial algebra, prove surjectivity by the left counit spanning formula,
and apply the affine closed immersion criterion. Finiteness supplies the affineness proof
passed to that predicate; it is not an additional assumption.
-/
theorem finite_group_faithful_regular_matrices
    (k : CommRingCat.{u}) (hk : IsField k) (G : Scheme.{u}) [G.Over (Spec k)]
    [GrpObj (G.asOver (Spec k))] [IsFinite (G ↘ Spec k)] :
    FiniteGroupRegularMatrices k G (isAffine_of_isAffineHom (G ↘ Spec k)) := by
  sorry

end AlgebraicGeometry
