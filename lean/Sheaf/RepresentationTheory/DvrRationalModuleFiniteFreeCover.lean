module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.RingHom.Flat

/-! # Finite free covers of rational modules over a DVR

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
Definition 9.2.2 and Remarks 9.2.3 and 9.2.4(i), printed p.521.
(blueprint: lem-sfb-dvr-rational-module-finite-free-cover)

The coalgebra structure on global sections is the canonical one constructed in
Mathlib.AlgebraicGeometry.Group.Affine from the given group-object diagrams.
Rational modules are expressed by their coaction maps and the two coaction equations.
-/

set_option autoImplicit false

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Every finite rational module for a flat affine finitely presented group scheme over
 a DVR is an equivariant quotient of a module with a finite basis.

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
Definition 9.2.2 and Remarks 9.2.3 and 9.2.4(i), printed p.521.
(blueprint: lem-sfb-dvr-rational-module-finite-free-cover)

Proof:
1. The affine flatness criterion (lem-weil-pbc-flat-morphism-affine-criterion) makes
   C = Gamma(H, O_H) flat over A. Tensoring multiplication by any nonzero element of
   the domain A with C (def-weil-pbc-flat-ring-map) proves C is torsion free.
2. Choose generators n_i of N and the surjection q : F = A^r -> N. The cofree comodules
   B = F tensor C and D = N tensor C have coaction 1 tensor Delta. Tensor functoriality
   makes b = q tensor 1 equivariant, and coassociativity makes rho_N : N -> D equivariant.
   Give T = N direct-sum B its componentwise coaction and put f(n,z) = rho_N(n) - b(z).
   This is equivariant. These maps and the tensor/direct-sum identifications are defined
   on pure tensors using def-weil-pbc-module-tensor-product.
3. Tensor exactness (lem-weil-pbc-flat-tensor-exact) shows that ker(f) is stable.
   The stable-core construction (lem-sfb-flat-coalgebra-subcomodule-core) therefore
   gives W = ker(f) its restricted coaction. Its projections a : W -> N and c : W -> B
   are equivariant, since its inclusion in T is equivariant.
4. The projection a is surjective: lift every first factor in a finite pure-tensor
   expansion of rho_N(n) through q. The resulting z satisfies b(z) = rho_N(n).
   The projection c is injective: if z = 0, then rho_N(n) = 0, hence n = 0 by the counit.
5. A basis of F identifies B with C^r, which is torsion free by step 1. The injection c
   consequently proves W is torsion free.
6. Lift the finitely many generators n_i through a. Apply
   lem-sfb-dvr-comodule-finite-free-lattice to this finite subset of W. It supplies a
   finite free subcomodule P containing the lifts. Its inclusion followed by a gives
   the required equivariant surjection. If N = 0, take P = 0 and the empty basis.
-/
theorem exists_finite_basis_equivariant_surjection_of_dvr
    (A : CommRingCat.{u}) [IsDomain A] [IsDiscreteValuationRing A]
    (H : Scheme.{u}) [H.Over (Spec A)] [IsAffine H]
    [GrpObj (H.asOver (Spec A))] [Flat (H ↘ Spec A)]
    [LocallyOfFinitePresentation (H ↘ Spec A)]
    (N : Type v) [AddCommGroup N] [Module A N] [Module.Finite A N]
    (ρN : N →ₗ[A] N ⊗[A] Γ(H, ⊤))
    (hcoassoc :
      (TensorProduct.assoc A N Γ(H, ⊤) Γ(H, ⊤)).toLinearMap ∘ₗ
          ρN.rTensor Γ(H, ⊤) ∘ₗ ρN =
        (Coalgebra.comul (R := A) (A := Γ(H, ⊤))).lTensor N ∘ₗ ρN)
    (hcounit :
      (TensorProduct.rid A N).toLinearMap ∘ₗ
          (Coalgebra.counit (R := A) (A := Γ(H, ⊤))).lTensor N ∘ₗ ρN =
        LinearMap.id) :
    ∃ (P : ModuleCat.{u} A) (n : ℕ) (_ : Module.Basis (Fin n) A P)
      (ρP : P →ₗ[A] P ⊗[A] Γ(H, ⊤)) (p : P →ₗ[A] N),
      (TensorProduct.assoc A P Γ(H, ⊤) Γ(H, ⊤)).toLinearMap ∘ₗ
          ρP.rTensor Γ(H, ⊤) ∘ₗ ρP =
        (Coalgebra.comul (R := A) (A := Γ(H, ⊤))).lTensor P ∘ₗ ρP ∧
      (TensorProduct.rid A P).toLinearMap ∘ₗ
          (Coalgebra.counit (R := A) (A := Γ(H, ⊤))).lTensor P ∘ₗ ρP =
        LinearMap.id ∧
      Function.Surjective p ∧ p.rTensor Γ(H, ⊤) ∘ₗ ρP = ρN ∘ₗ p := by
  sorry

end AlgebraicGeometry
