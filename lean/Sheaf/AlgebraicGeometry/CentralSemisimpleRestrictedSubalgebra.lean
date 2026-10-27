module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.IsDiag

import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Central semisimple tangent vectors form a restricted subalgebra

Source: Milne, Algebraic Groups (2017), Proposition 17.80, first reduction,
printed p.378, and Corollary 17.77, printed p.377
(blueprint: lem-sfb-central-semisimple-restricted-subalgebra).

We use the canonical tangent Lie algebra and the differential of the specified closed
representation. Scalar extensions are realized faithfully as spans in matrix spaces.
Diagonalizability means conjugacy to a diagonal matrix over the algebraic closure.
Restricted closure is expressed by existence of a tangent vector with matrix X^p;
the faithful differential identifies this uniquely with the canonical restricted power.
Triviality of the adjoint representation means commutation on every algebra of points,
including nonreduced algebras, on the whole scalar-extended subspace.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- Under geometric centrality of all semisimple tangent vectors, a nonnilpotent smooth
connected affine group has positive characteristic and the asserted restricted fixed subspace.
Source: Milne, Algebraic Groups (2017), Proposition 17.80, p.378, and Corollary 17.77,
p.377 (blueprint: lem-sfb-central-semisimple-restricted-subalgebra).

Proof:
1. If the characteristic were zero, use lem-sfb-algebraic-lie-additive-jordan to write
   each Y as Y_s + Y_n. Geometric centrality kills ad(Y_s), while rational differentiation
   makes ad(Y_n) nilpotent. Apply lem-sfb-charzero-ad-nilpotence-group-criterion:
   J would be nilpotent, a contradiction. Thus the characteristic is a prime p > 0.
2. The faithful closed representation has injective differential. The centre Z of its
   tangent Lie algebra is the solution space of homogeneous linear commutator equations;
   those equations also show that formation of Z commutes with field extension.
   By lem-sfb-restricted-rational-differentiation, matrix p-th power is the canonical
   restricted operation and ad(X^[p]) = ad(X)^p. Thus Z is closed under that operation.
3. Apply lem-sfb-commuting-p-power-stable-image to the commuting matrix space Z.
   Its stable image is precisely the set of geometrically diagonalizable matrices in Z.
   Geometric centrality identifies this with all semisimple vectors of Lie(J).
   The same argument after scalar extension gives exactly all geometric semisimple
   vectors. Brackets vanish in Z, and the stable image is closed under p-th powers.
4. For each such X, lem-sfb-semisimple-tangent-stabilizer gives a smooth closed
   stabilizer C with full tangent space. The identity section makes J geometrically
   connected by lem-sbc-connected-rational-point-geometrically-connected. Over the
   algebraic closure, lem-sfb-finite-type-group-identity-subgroup gives C's open identity
   component, smooth by lem-pc-open-immersion-smooth-composition. Its tangent space is
   still full, using the scalar-extension calculation in
   lem-sfb-affine-group-lie-tangent-calculus. Apply
   lem-sfb-smooth-subgroup-tangent-generation to obtain C = J geometrically.
   Faithfully flat field extension detects vanishing of the ideal of C, so C = J over k.
5. A k-basis of the semisimple subspace is therefore fixed on every algebra of points.
   A-linearity fixes its entire scalar extension. In the faithful representation this
   is exactly commutation of each group matrix with every matrix in the displayed span.
   The argument includes the zero-dimensional subspace.
-/
theorem central_semisimple_restricted_subalgebra
    (k : Type u) [Field k]
    (J : Grp (Over (Spec (.of k))))
    (n : Type u) [Fintype n] [DecidableEq n]
    (r : GeneralLinearGroup.RationalHom J.X n) [IsMonHom r]
    [IsClosedImmersion r.left]
    (haff : IsAffine J.X.left)
    (hft : LocallyOfFiniteType J.X.hom) (hqc : QuasiCompact J.X.hom)
    (hsm : Smooth J.X.hom) (hconn : ConnectedSpace J.X.left)
    (hnil : ¬ ∃ (m : ℕ) (C : Fin (m + 1) → Grp (Over (Spec (.of k))))
      (i : ∀ j : Fin (m + 1), C j ⟶ J),
      (∀ j : Fin (m + 1), IsClosedSubgroupScheme (i j).hom.hom ∧
        IsNormalSubgroupScheme (i j).hom.hom) ∧
      IsIso (i 0) ∧ Nonempty (C (Fin.last m) ≅ Grp.trivial _) ∧
      (∀ j : Fin m, ∃ l : C j.succ ⟶ C j.castSucc, l ≫ i j.castSucc = i j.succ) ∧
      ∀ (j : Fin m) (A : Type u) [CommRing A] [Algebra k A]
        (g : points J.X A) (c : points (C j.castSucc).X A),
        ∃ z : points (C j.succ).X A,
          z ≫ (i j.succ).hom.hom =
            g * (c ≫ (i j.castSucc).hom.hom) * g⁻¹ *
              (c ≫ (i j.castSucc).hom.hom)⁻¹)
    (hcentral : ∀ X ∈ Submodule.span (AlgebraicClosure k)
      (Set.range fun x : GrpObj.Lie J.X ↦
        (r.differential x).map (algebraMap k (AlgebraicClosure k))),
      (∃ P : (Matrix n n (AlgebraicClosure k))ˣ,
        ((↑(P⁻¹) : Matrix n n (AlgebraicClosure k)) * X *
          (↑P : Matrix n n (AlgebraicClosure k))).IsDiag) →
      ∀ Y ∈ Submodule.span (AlgebraicClosure k)
        (Set.range fun y : GrpObj.Lie J.X ↦
          (r.differential y).map (algebraMap k (AlgebraicClosure k))), Commute X Y) :
    ∃ p : ℕ, p.Prime ∧ CharP k p ∧
      ∃ S : LieSubalgebra k (GrpObj.Lie J.X),
        (∀ x : GrpObj.Lie J.X, x ∈ S ↔
          ∃ P : (Matrix n n (AlgebraicClosure k))ˣ,
            ((↑(P⁻¹) : Matrix n n (AlgebraicClosure k)) *
              (r.differential x).map (algebraMap k (AlgebraicClosure k)) *
              (↑P : Matrix n n (AlgebraicClosure k))).IsDiag) ∧
        (∀ x ∈ S, ∃ y ∈ S, r.differential y = r.differential x ^ p) ∧
        (∀ (A : Type u) [CommRing A] [Algebra k A]
          (g : points J.X A) (X : Matrix n n A),
          X ∈ Submodule.span A
            ((fun x : GrpObj.Lie J.X ↦ (r.differential x).map (algebraMap k A)) ''
              (S : Set (GrpObj.Lie J.X))) →
          Commute (r.points A g : Matrix n n A) X) ∧
        (∀ X ∈ Submodule.span (AlgebraicClosure k)
          (Set.range fun x : GrpObj.Lie J.X ↦
            (r.differential x).map (algebraMap k (AlgebraicClosure k))),
          (∃ P : (Matrix n n (AlgebraicClosure k))ˣ,
            ((↑(P⁻¹) : Matrix n n (AlgebraicClosure k)) * X *
              (↑P : Matrix n n (AlgebraicClosure k))).IsDiag) ↔
          X ∈ Submodule.span (AlgebraicClosure k)
            ((fun x : GrpObj.Lie J.X ↦
              (r.differential x).map (algebraMap k (AlgebraicClosure k))) ''
                (S : Set (GrpObj.Lie J.X)))) := by
  sorry

end AlgebraicGeometry
