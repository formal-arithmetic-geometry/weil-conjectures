/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.DualNumber
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential
public import WeilConjectures.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.CategoryTheory.Yoneda

/-!
# Scalar-extended infinitesimal points and the adjoint action

Source: Milne, Algebraic Groups (2017), 10.6,10.11,10.14,10.18--10.21, pp.188--193
(blueprint: lem-sfb-affine-group-dual-number-calculus).

We use the existing `GrpObj.Lie G.X` model of the tangent space at the identity.
`GrpObj.lieIdentityTangentEquiv` identifies it canonically and linearly with the recorded
`schemeTangentSpace`, after the canonical identity residue-field identification. Its tangent
point is `GrpObj.tangentPoint`, so normalization below fixes the actual tangent vectors.

Scalar extension is written R tensor Lie, the Mathlib order, related to the node's Lie tensor R
by tensor symmetry. `Data` packages the bijections and adjoint action, with their defining
normalization. `regular` realizes that action by an actual group-scheme morphism in every
basis, including the empty basis. `Compatible` packages functoriality and subgroup intersection.
The sole theorem supplies these packages simultaneously for all affine finite-type groups.
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.AffineGroupDualNumberCalculus

variable {k : Type u} [Field k]

/-- Apply a k-algebra homomorphism to both coefficients of a dual number.
This is the existing `DualNumber.mapRingHom`, bundled over k.
Source: Milne 10.19 (blueprint: lem-sfb-affine-group-dual-number-calculus). -/
noncomputable def dualMap {R S : Type u} [CommRing R] [Algebra k R]
    [CommRing S] [Algebra k S] (h : R →ₐ[k] S) : DualNumber R →ₐ[k] DualNumber S where
  __ := DualNumber.mapRingHom h.toRingHom
  commutes' a := by
    ext <;> simp [DualNumber.mapRingHom, TrivSqZeroExt.algebraMap_eq_inl']

/-- The projection setting the square-zero coordinate to zero, with scalars restricted to k.
Source: Milne 10.18 (blueprint: lem-sfb-affine-group-dual-number-calculus). -/
noncomputable def reduction (R : Type u) [CommRing R] [Algebra k R] :
    DualNumber R →ₐ[k] R :=
  (TrivSqZeroExt.fstHom R R R).restrictScalars k

/-- Exactly the dual-number points reducing to the identity, with no condition on R.
Source: Milne 10.18 (blueprint: lem-sfb-affine-group-dual-number-calculus). -/
abbrev Kernel (G : Grp (Over (Spec (.of k)))) (R : Type u) [CommRing R] [Algebra k R] :=
  {x : points G.X (DualNumber R) // points.map G.X (reduction R) x = 1}

/-- The conclusions for one group, including algebraicity of its conjugation representation.
The normalization, additivity, scaling and coefficient naturality fix E on every pure tensor;
the conjugation identity then fixes Ad. No arbitrary map is substituted for either construction.
Source: Milne 10.6,10.11,10.18--10.21
(blueprint: lem-sfb-affine-group-dual-number-calculus). -/
structure Data (G : Grp (Over (Spec (.of k)))) where
  /-- Finite dimension of the identity tangent space. -/
  finite : Module.Finite k (GrpObj.Lie G.X)
  /-- The canonical scalar-extended tangent-point bijection. -/
  E (R : Type u) [CommRing R] [Algebra k R] :
    (R ⊗[k] GrpObj.Lie G.X) ≃ Kernel G R
  /-- Tangent addition is multiplication of kernel points. -/
  add (R : Type u) [CommRing R] [Algebra k R] (v w : R ⊗[k] GrpObj.Lie G.X) :
    (E R (v + w)).val = (E R v).val * (E R w).val
  /-- The zero tangent vector is the identity point. -/
  zero (R : Type u) [CommRing R] [Algebra k R] : (E R 0).val = 1
  /-- Tangent negation is inversion. -/
  neg (R : Type u) [CommRing R] [Algebra k R] (v : R ⊗[k] GrpObj.Lie G.X) :
    (E R (-v)).val = ((E R v).val)⁻¹
  /-- Scaling the square-zero coordinate scales the tangent vector. -/
  scale (R : Type u) [CommRing R] [Algebra k R] (a : R)
      (v : R ⊗[k] GrpObj.Lie G.X) :
    points.map G.X ((DualNumber.scale a).restrictScalars k) (E R v).val =
      (E R (a • v)).val
  /-- Over k the bijection is the defining tangent identification. -/
  normalize (v : GrpObj.Lie G.X) :
    (E k (1 ⊗ₜ[k] v)).val = GrpObj.tangentPoint v
  /-- Naturality under every homomorphism of test algebras. -/
  natural (R S : Type u) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
      (h : R →ₐ[k] S) (v : R ⊗[k] GrpObj.Lie G.X) :
    points.map G.X (dualMap h) (E R v).val =
      (E S (TensorProduct.map h.toLinearMap (LinearMap.id) v)).val
  /-- The adjoint action takes values in invertible R-linear maps. -/
  Ad (R : Type u) [CommRing R] [Algebra k R] :
    points G.X R →* LinearMap.GeneralLinearGroup R (R ⊗[k] GrpObj.Lie G.X)
  /-- Ad is characterized by conjugation using the constant lift of j. -/
  conjugation (R : Type u) [CommRing R] [Algebra k R]
      (j : points G.X R) (v : R ⊗[k] GrpObj.Lie G.X) :
    points.map G.X (TrivSqZeroExt.inlAlgHom k R R) j * (E R v).val *
        (points.map G.X (TrivSqZeroExt.inlAlgHom k R R) j)⁻¹ =
      (E R ((Ad R j).toLinearEquiv v)).val
  /-- In every finite basis Ad is induced by a unique group-scheme homomorphism. -/
  regular (n : ℕ) (b : Module.Basis (ULift.{u} (Fin n)) k (GrpObj.Lie G.X)) :
    ∃! ρ : G.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k, IsMonHom ρ ∧
      ∀ (R : Type u) [CommRing R] [Algebra k R] (j : points G.X R),
        Ad R j = Matrix.GeneralLinearGroup.toLin' (b.baseChange R)
          (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k R (j ≫ ρ))

/-- Functoriality and the closed-subgroup intersection for two instances of the calculus.
Source: Milne, Algebraic Groups, 10.14 and 10.19--10.21, pp.190,192--193
(blueprint: lem-sfb-affine-group-dual-number-calculus). -/
structure Compatible {G H : Grp (Over (Spec (.of k)))}
    (D : Data G) (D' : Data H) (f : G.X ⟶ H.X) [IsMonHom f] : Prop where
  /-- The scalar-extended differential gives postcomposition on infinitesimal points. -/
  differential (R : Type u) [CommRing R] [Algebra k R]
      (v : R ⊗[k] GrpObj.Lie G.X) :
    (D.E R v).val ≫ f =
      (D'.E R (LinearMap.baseChange R (GrpObj.differential f).toLinearMap v)).val
  /-- A closed inclusion has injective differential and the stated intersection image. -/
  closed (hi : IsClosedSubgroupScheme f) :
    Function.Injective (GrpObj.differential f) ∧
      ∀ (R : Type u) [CommRing R] [Algebra k R],
        Set.range (fun v : R ⊗[k] GrpObj.Lie G.X ↦
          (D'.E R (LinearMap.baseChange R (GrpObj.differential f).toLinearMap v)).val) =
          Set.range (fun b : points G.X (DualNumber R) ↦ b ≫ f) ∩
            {x | points.map H.X (reduction R) x = 1}
  /-- The differential intertwines conjugation by all algebra-valued points. -/
  equivariant (R : Type u) [CommRing R] [Algebra k R]
      (j : points G.X R) (v : R ⊗[k] GrpObj.Lie G.X) :
    LinearMap.baseChange R (GrpObj.differential f).toLinearMap
        ((D.Ad R j).toLinearEquiv v) =
      (D'.Ad R (j ≫ f)).toLinearEquiv
        (LinearMap.baseChange R (GrpObj.differential f).toLinearMap v)

/-- Scalar-extended tangent points, their group operations, and the algebraic adjoint action.
Source: Milne, Algebraic Groups, 10.6,10.11,10.14,10.18--10.21, pp.188--193
(blueprint: lem-sfb-affine-group-dual-number-calculus).

Proof (the twelve steps of the DAG node):
1. Use the coordinate Hopf algebra of the affine group, and the affine-pair finite-type
criterion, to write its coordinate algebra A with finitely many generators. Write I=ker(epsilon).
2. The split augmentation identifies A/I^2 with k plus I/I^2. Subtract the counits of the
chosen generators; their classes span I/I^2. The finite-dual dimension result gives finiteness
of its dual.
3. A point reducing to the identity has the unique form epsilon + delta*d. Multiplicativity
is the counit Leibniz rule, so d factors through I/I^2. Conversely each functional gives a
point by this formula, including for the zero test algebra.
4. At k this is the defining tangent identification. Addition and scaling agree with the
canonical dual-number operations. Precomposition by the coordinate map gives the differential.
5. Apply finite-projective tensor--Hom to I/I^2, which is projective by a finite basis.
Tensor symmetry and the unit isomorphism give E, with coefficient (r tensor v)(z)=r*v(z).
6. Expand convolution using the coproduct. Delta squared vanishes; the two counit identities
leave the sum of coefficients. Zero and negatives give the identity and inverse. Scaling the
square-zero coordinate scales the coefficient.
7. Algebra maps preserve the coefficient formula on pure tensors. A group homomorphism
preserves the counit and its ideal square, giving compatibility with its linear differential.
8. A closed subgroup has quotient coordinate algebra and injective points. Its differential
is injective and has a linear left inverse over the field, hence remains injective after tensor.
Injectivity on R-points says that its intersection with the ambient kernel is its own kernel.
9. Conjugation has coefficient sum j(a1)*d(a2)*j(S(a3)), an R-linear expression with inverse
conjugation by j inverse. It is natural in R.
10. In any finite basis evaluate this expression at the universal point. The resulting
invertible matrix gives a morphism to the existing general linear group scheme. In dimension
zero the empty matrix group represents the unique automorphism of the zero module.
11. Conjugation respects products and identity. Fully faithful affine Yoneda makes the
morphism a group homomorphism, unique from this formula and independent of the basis.
12. Apply f to j*E(v)*j inverse. Naturality of E and its injectivity give adjoint equivariance.
No smoothness, reducedness, connectedness, or characteristic restriction is used. -/
theorem exists_compatible_calculus :
    ∃ D : ∀ (G : Grp (Over (Spec (.of k)))) [IsAffine G.X.left]
        [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom], Data G,
      ∀ (G H : Grp (Over (Spec (.of k)))) [IsAffine G.X.left]
        [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [IsAffine H.X.left]
        [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
        (f : G.X ⟶ H.X) [IsMonHom f], Compatible (D G) (D H) f := by
  sorry

end AlgebraicGeometry.AffineGroupDualNumberCalculus
