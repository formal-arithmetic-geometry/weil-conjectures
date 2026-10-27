/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.AlgebraicGeometry.DiagonalizableGroup
public import Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.GroupTheory.Finiteness
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Weight grading of a diagonalizable group representation

Source: Milne, Algebraic Groups (2017), Theorem 12.12 and Remark 12.13, pp.234--235.
(blueprint: lem-sfb-diagonalizable-representation-weight-grading)

The scalar extension is A tensor V, canonically symmetric to V tensor A in the node.
The fixed finite basis only realizes GL(V) by the existing matrix group scheme; it is
not a basis of weight vectors. Weight spaces are defined by all algebra-valued points.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.DiagonalizableRepresentation

variable {k : Type u} [Field k] {M : Type u} [AddCommGroup M]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A morphism to GL(V), realized in the canonical finite basis, including dimension zero.
Source: Milne, Definition 12.11 and Remark 12.13, pp.234--235
(blueprint: lem-sfb-diagonalizable-representation-weight-grading). -/
abbrev Representation :=
  GeneralLinearGroup.RationalHom (diagonalizableGroup k M).X
    (RationalRepresentation.FiniteIndex (k := k) V)

/-- The value of the character dual to t maps to e_m: evaluate e_m at the given point.
Source: Milne, Remark 12.13, p.235
(blueprint: lem-sfb-diagonalizable-representation-weight-grading). -/
def characterValue (m : M) (A : Type u) [CommRing A] [Algebra k A]
    (x : points (diagonalizableGroup k M).X A) : A :=
  (Spec.mapMulEquiv.symm x).ofConv (AddMonoidAlgebra.single m (1 : k))

/-- The actual automorphism on A tensor V induced by a scheme morphism to GL(V).
Source: Milne, Definition 12.11, p.234; Remark 4.1, p.84
(blueprint: lem-sfb-diagonalizable-representation-weight-grading). -/
def pointAction (rho : Representation (k := k) (M := M) (V := V))
    (A : Type u) [CommRing A] [Algebra k A]
    (x : points (diagonalizableGroup k M).X A) : A ⊗[k] V ≃ₗ[A] A ⊗[k] V :=
  (Matrix.GeneralLinearGroup.toLin' ((RationalRepresentation.finiteBasis (k := k) V).baseChange A)
    (GeneralLinearGroup.homMulEquiv (RationalRepresentation.FiniteIndex (k := k) V) k A
      (x ≫ rho))).toLinearEquiv

/-- The simultaneous all-algebras eigenspace: rho_A(x)(1 tensor v) = chi_m(x) tensor v.
The intersection of equalizers is a genuine submodule, with no postponed data or proofs.
Source: Milne, Theorem 12.12(d) and Remark 12.13, pp.234--235
(blueprint: lem-sfb-diagonalizable-representation-weight-grading). -/
def weightSpace (rho : Representation (k := k) (M := M) (V := V)) (m : M) :
    Submodule k V :=
  ⨅ (A : Type u) (_ : CommRing A) (_ : Algebra k A)
    (x : points (diagonalizableGroup k M).X A),
    LinearMap.eqLocus
      ((pointAction rho A x).toLinearMap.restrictScalars k ∘ₗ TensorProduct.mk k A V 1)
      (TensorProduct.mk k A V (characterValue m A x))

/-- The sum of the weight inclusions over k, on finite-support families.
Source: Milne, Theorem 12.12(d), pp.234--235
(blueprint: lem-sfb-diagonalizable-representation-weight-grading). -/
def weightSum (rho : Representation (k := k) (M := M) (V := V)) :
    (DirectSum M (fun m : M ↦ weightSpace rho m)) →ₗ[k] V := by
  classical
  exact DirectSum.coeLinearMap (weightSpace rho)

/-- The canonical inclusion of the scalar extension of a weight subspace.
Source: Milne, Theorem 12.12, p.235, coefficient-projection argument
(blueprint: lem-sfb-diagonalizable-representation-weight-grading). -/
def summandMap (rho : Representation (k := k) (M := M) (V := V))
    (A : Type u) [CommRing A] [Algebra k A] (m : M) :
    A ⊗[k] weightSpace rho m →ₗ[A] A ⊗[k] V :=
  (weightSpace rho m).subtype.baseChange A

/-- The sum of the actual base-changed inclusions, rather than an unspecified isomorphism.
Source: Milne, Theorem 12.12, p.235, coefficient-projection argument
(blueprint: lem-sfb-diagonalizable-representation-weight-grading). -/
def sumMap (rho : Representation (k := k) (M := M) (V := V))
    (A : Type u) [CommRing A] [Algebra k A] :
    (DirectSum M (fun m : M ↦ A ⊗[k] weightSpace rho m)) →ₗ[A] A ⊗[k] V := by
  classical
  exact DirectSum.toModule A M (A ⊗[k] V) (summandMap rho A)

/-- Extension of an A-linear endomorphism to B tensor V, conjugated by the canonical
cancellation B tensor_A (A tensor_k V) = B tensor_k V.
Source: Milne, Theorem 12.12 and Remark 12.13, p.235, coefficient argument
(blueprint: lem-sfb-diagonalizable-representation-weight-grading). -/
def extendEnd (A B : Type u) [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (f : A ⊗[k] V →ₗ[A] A ⊗[k] V) : B ⊗[k] V →ₗ[B] B ⊗[k] V :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange k A B B V).toLinearMap ∘ₗ
    f.baseChange B ∘ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k A B B V).symm.toLinearMap

/-- Finite weight grading, its arbitrary scalar extensions, and preservation by all-algebras
commutants. No reducedness, characteristic restriction, or nonzero dimension is assumed.
Source: Milne, Theorem 12.12(a) implies (d) and Remark 12.13, pp.234--235
(blueprint: lem-sfb-diagonalizable-representation-weight-grading).

Proof, following the nine steps of the node:
1. Finite generators of M and their negatives generate k[M] as an algebra, so D(M) is
   finite type (def-weil-finite-type-morphism). The finite dictionary and comodule dictionary
   of lem-sfb-rational-representation-comodule-dictionary give the coaction c and its
   universal-point formula, including V = 0.
2. Extract the e_m coefficient in the second tensor factor using the tensor universal
   property (def-weil-pbc-module-tensor-product), obtaining linear maps p_m and the unique
   finite expansion c(v) = sum_m p_m(v) tensor e_m.
3. Coassociativity gives c(p_m(v)) = p_m(v) tensor e_m. The counit gives sum_m p_m(v) = v.
   Comparing coefficients gives p_m p_n = delta_mn p_n.
4. The all-algebras formula identifies this equation with membership in weightSpace;
   its reverse direction tests at k[M] and the universal point id. Thus p_m has image V_m
   and is the identity on V_m.
5. The sum map on finite-support families (def-weil-pbc-direct-sum-modules) has inverse
   v maps to (p_m(v))_m. A finite spanning list (def-weil-finite-dimensional-subspace)
   bounds all coefficient supports by one finite set, outside which V_m = 0.
6. Tensor the inclusions and projections with A. The sumMap inverse sends a tensor v
   to the finite family of tensors p_m(v). Checking both composites on pure tensors gives
   bijectivity over every A, without a flatness assumption.
7. Evaluating c(w) = w tensor e_m shows that rho_A(x) acts on the entire extended
   summand by the scalar characterValue m A x. Applying this to every A-algebra B gives
   the action of the base-changed group scheme, not only its A-points.
8. For a commuting endomorphism f use B = A[M] and the universal point e_m maps to e_m.
   After the explicit tensor cancellation in extendEnd, coefficient extraction yields
   P_m f = f P_m. Since P_m is the identity on its summand, f preserves that summand.
9. For M = 0 there is just the identity weight; for V = 0 all summands are zero.
   The zero test algebra also gives zero tensors. Even in characteristic torsion the e_m
   are distinct formal basis vectors: the argument never divides by the group order or
   replaces all algebra-valued points by k-points.
-/
theorem weightGrading [AddGroup.FG M]
    (rho : Representation (k := k) (M := M) (V := V)) [IsMonHom rho] :
    {m : M | weightSpace rho m ≠ ⊥}.Finite ∧
    (Function.Bijective (weightSum rho)) ∧
    (∀ (A : Type u) [CommRing A] [Algebra k A],
      Function.Bijective (sumMap rho A) ∧
      (∀ (m : M) (x : points (diagonalizableGroup k M).X A)
        (z : A ⊗[k] weightSpace rho m),
        pointAction rho A x (summandMap rho A m z) =
          characterValue m A x • summandMap rho A m z) ∧
      ∀ (f : A ⊗[k] V →ₗ[A] A ⊗[k] V),
        (∀ (B : Type u) [CommRing B] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
          (x : points (diagonalizableGroup k M).X B),
          extendEnd A B f ∘ₗ (pointAction rho B x).toLinearMap =
            (pointAction rho B x).toLinearMap ∘ₗ extendEnd A B f) →
        ∀ m : M, Set.MapsTo f (summandMap rho A m).range (summandMap rho A m).range) := by
  sorry

end AlgebraicGeometry.DiagonalizableRepresentation
