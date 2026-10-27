module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Basic

import Sheaf.AlgebraicGeometry.HopfCoactionLinearization
import Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Faithful representations with central split-torus weight blocks

Source: Milne, Algebraic Groups (2017), Theorem 4.9 and Corollary 4.10, p.87;
Theorem 12.12 and Remark 12.13, pp.234--235; Proposition 12.46(a), proof, p.246
(blueprint: lem-sfb-central-torus-faithful-weight-blocks).

The finite-dimensional space is a finite coordinate space. We use its standard basis
only to identify the existing general linear group scheme with its automorphism functor.
Scalar extensions are A tensor_F V, canonically symmetric to V tensor_F A.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct CategoryTheory.MonObj

namespace AlgebraicGeometry.CentralTorusWeightBlocks

/-- The actual action of a matrix-valued scheme morphism on the scalar extension of
its coordinate space, using the base-changed standard basis.
Source: Milne, Chapter 4(a), pp.83--84
(blueprint: lem-sfb-central-torus-faithful-weight-blocks). -/
def pointAction {F : Type u} [Field F] {n : Type u} [Fintype n] [DecidableEq n]
    {H : Over (Spec (.of F))} (ρ : H ⟶ GeneralLinearGroup n F)
    (A : Type u) [CommRing A] [Algebra F A]
    (h : (Spec (.of A)).asOver (Spec (.of F)) ⟶ H) :
    A ⊗[F] (n → F) ≃ₗ[A] A ⊗[F] (n → F) :=
  (Matrix.GeneralLinearGroup.toLin' ((Pi.basisFun F n).baseChange A)
    (GeneralLinearGroup.homMulEquiv n F A (h ≫ ρ))).toLinearEquiv

/-- Evaluation of a character at an algebra-valued point: pull back the Laurent
coordinate t and use the canonical global-sections identification for Spec A.
Source: Milne, Chapter 12(a)--(d), pp.230--235
(blueprint: lem-sfb-central-torus-faithful-weight-blocks). -/
def characterScalar {F : Type u} [Field F] {T : Grp (Over (Spec (.of F)))}
    (χ : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (A : Type u) [CommRing A] [Algebra F A]
    (t : (Spec (.of A)).asOver (Spec (.of F)) ⟶ T.X) : A :=
  (Scheme.ΓSpecIso (.of A)).hom
    ((t ≫ χ.hom.hom).left.appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial F))).inv (LaurentPolynomial.T 1)))

/-- An affine finite-type group has a faithful nonzero representation with nonzero,
H-stable scalar weight blocks for any central split torus, and its character tuple
is a closed immersion.
Source: Milne, Theorem 4.9 and Corollary 4.10, p.87; Theorem 12.12 and Remark 12.13,
pp.234--235; Proposition 12.46(a), proof, p.246
(blueprint: lem-sfb-central-torus-faithful-weight-blocks).

Proof, following the five steps of the node:
1. Write C = F[H]. The affine-pair criterion lem-weil-pbc-lft-affine-pairs makes
   C finitely generated over F. By lem-sfb-comodule-finite-subrepresentation choose
   a finite-dimensional subcomodule containing 1 and algebra generators of C.
   The counit shows it is nonzero. Retain a basis from a finite spanning list,
   using def-weil-finite-dimensional-subspace and def-weil-pbc-free-module.
2. Apply lem-sfb-hopf-coaction-linearization to obtain the representation. Its
   matrix coefficients a_ij satisfy the group laws and have invertible determinant.
   The coordinate map of def-sc-general-linear-group is surjective because
   e_j = sum_i epsilon(e_i) a_ij, so its image contains the chosen generators.
   Thus the homomorphism is a closed immersion, including for nonreduced H.
3. For one coordinate G_m of T apply lem-sfb-gm-representation-weight-basis.
   For any A and h in H(A), extend to A[z,z^-1]. Centrality gives
   sum_b u_b z^b = z^a sum_b u_b for the components of h(w), with w of weight a.
   Laurent coefficient maps (def-weil-laurent-polynomial-ring), extended using
   def-weil-pbc-module-tensor-product, give u_b = 0 for b distinct from a.
   Applying this also to h inverse proves stability by automorphisms over every A.
4. Iterate through the r factors, discarding zero summands. The finite direct
   sum remains H-stable. The weight tuple defines the character product t_j^a_ij
   using def-sc-gm-ga. For r = 0 keep the single nonzero block and trivial character.
5. Choose a basis in each block. The map F[GL(V)] to F[T] is surjective because
   both closed immersions induce surjections. Its matrix-coordinate formula factors
   through F[y_1^+-1,...,y_s^+-1], sending diagonal entries in block i to y_i,
   off-diagonal entries to zero and det inverse to product_i y_i^(-dim V_i).
   Hence the character-tuple coordinate map is surjective. The affine tensor
   pushout universal property identifies this Laurent algebra with the coordinate
   algebra of the product of G_m. Thus the character tuple is a closed immersion.
-/
theorem exists_faithful_weight_blocks
    {F : Type u} [Field F] [IsAlgClosed F]
    (H T : Grp (Over (Spec (.of F))))
    [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    (iT : T ⟶ H) [IsClosedSubgroupScheme iT.hom.hom]
    (r : ℕ) (hsplit : Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (hcentral : ∀ (A : Type u) [CommRing A] [Algebra F A]
      (t : (Spec (.of A)).asOver (Spec (.of F)) ⟶ T.X)
      (h : (Spec (.of A)).asOver (Spec (.of F)) ⟶ H.X),
      Commute (t ≫ iT.hom.hom) h) :
    ∃ (N : ℕ) (_ : 0 < N)
      (ρ : H ⟶ Grp.mk (GeneralLinearGroup (ULift.{u} (Fin N)) F))
      (s : ℕ) (V : Fin s → Submodule F (ULift.{u} (Fin N) → F))
      (χ : Fin s → (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))),
      IsClosedImmersion ρ.hom.hom.left ∧
      DirectSum.IsInternal V ∧ (∀ i : Fin s, V i ≠ ⊥) ∧
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (h : (Spec (.of A)).asOver (Spec (.of F)) ⟶ H.X)
        (i : Fin s) (v : A ⊗[F] (ULift.{u} (Fin N) → F)),
        v ∈ (V i).baseChange A →
          pointAction ρ.hom.hom A h v ∈ (V i).baseChange A) ∧
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (t : (Spec (.of A)).asOver (Spec (.of F)) ⟶ T.X)
        (i : Fin s) (v : A ⊗[F] (ULift.{u} (Fin N) → F)),
        v ∈ (V i).baseChange A →
          pointAction ρ.hom.hom A (t ≫ iT.hom.hom) v = characterScalar (χ i) A t • v) ∧
      IsClosedImmersion (Pi.lift (fun i : Fin s ↦ (χ i).hom.hom)).left := by
  sorry

end AlgebraicGeometry.CentralTorusWeightBlocks
