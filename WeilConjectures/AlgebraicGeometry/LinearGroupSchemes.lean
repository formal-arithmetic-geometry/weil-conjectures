/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import WeilConjectures.AlgebraicGeometry.StandardGroupSchemes
import WeilConjectures.LinearAlgebra.Matrix.CauchyBinet

/-!
# General and special linear group schemes

Source: the current Weil conjectures blueprint, sec-smooth-purity/sk-prop-an,
def-sc-general-linear-group; Stacks Project, Tags 022W and 022X.
(blueprint: def-sc-general-linear-group)

The general linear scheme and its Hopf algebra are the existing upstream constructions.
The special linear scheme is the polynomial quotient by det - 1, with explicit descended
coordinate maps. The group structure is selected only from a unique-existence statement
fixing all its data. The finite index type is lifted to the field's universe so that the
upstream group scheme and all test algebras have the same size convention.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.LinearGroupSchemes

/-- The c matrix indices, lifted for the universe of the base field.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
-/
abbrev Index (c : ℕ) := ULift.{u} (Fin c)

variable (k : Type u) [Field k] (c : ℕ)

/-- The ideal (det X - 1) in the polynomial ring of matrix entries.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
-/
noncomputable def specialIdeal : Ideal (MvPolynomial (Index.{u} c × Index.{u} c) k) :=
  Ideal.span { (Matrix.GeneralLinearGroup.genericMatrix (Index.{u} c) k).det - 1 }

/-- The actual coordinate algebra k[x_ij]/(det X - 1), including nonreduced test algebras.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
-/
abbrev SpecialAlgebra := MvPolynomial (Index.{u} c × Index.{u} c) k ⧸ specialIdeal k c

/-- The residue of the generic matrix in the determinant-one quotient.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
-/
noncomputable def specialMatrix : Matrix (Index.{u} c) (Index.{u} c) (SpecialAlgebra k c) :=
  fun i j ↦ Ideal.Quotient.mkₐ k (specialIdeal k c) (MvPolynomial.X (i, j))

/-- The special linear scheme, with precisely the displayed polynomial quotient as coordinates.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
-/
noncomputable def specialLinear : Over (Spec (.of k)) :=
  StandardGroupSchemes.affine k (SpecialAlgebra k c)

/-- The three substitutions kill det - 1 and therefore descend to the quotient.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
Proof: square Cauchy--Binet gives det(UV)=det(U)det(V), and the residue generic matrix
has determinant 1. Thus the tensor product matrix has determinant 1, as does the identity.
The adjugate identity gives the inverse of the residue matrix, whose determinant is 1.
Each substitution kills det - 1 and every multiple, hence the generated ideal.
These are steps 1, 2, 7 and 8 of the node's proof. -/
theorem specialRelations :
    (∀ f ∈ specialIdeal k c,
      MvPolynomial.aeval (fun p : Index.{u} c × Index.{u} c ↦
        ∑ r, specialMatrix k c p.1 r ⊗ₜ[k] specialMatrix k c r p.2) f = 0) ∧
    (∀ f ∈ specialIdeal k c,
      MvPolynomial.aeval (fun p : Index.{u} c × Index.{u} c ↦
        (1 : Matrix (Index.{u} c) (Index.{u} c) k) p.1 p.2) f = 0) ∧
    (∀ f ∈ specialIdeal k c,
      MvPolynomial.aeval (fun p : Index.{u} c × Index.{u} c ↦
        (specialMatrix k c).adjugate p.1 p.2) f = 0) := by
  sorry

/-- The descended matrix-multiplication comultiplication.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
-/
noncomputable def specialComul : SpecialAlgebra k c →ₐ[k]
    SpecialAlgebra k c ⊗[k] SpecialAlgebra k c :=
  Ideal.Quotient.liftₐ (specialIdeal k c)
    (MvPolynomial.aeval (fun p ↦
      ∑ r, specialMatrix k c p.1 r ⊗ₜ[k] specialMatrix k c r p.2))
    (specialRelations k c).1

/-- The descended evaluation at the identity matrix.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
-/
noncomputable def specialCounit : SpecialAlgebra k c →ₐ[k] k :=
  Ideal.Quotient.liftₐ (specialIdeal k c)
    (MvPolynomial.aeval (fun p ↦ (1 : Matrix (Index.{u} c) (Index.{u} c) k) p.1 p.2))
    (specialRelations k c).2.1

/-- The descended inverse, equal to the adjugate since det X = 1 in this quotient.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
-/
noncomputable def specialAntipode : SpecialAlgebra k c →ₐ[k] SpecialAlgebra k c :=
  Ideal.Quotient.liftₐ (specialIdeal k c)
    (MvPolynomial.aeval (fun p ↦ (specialMatrix k c).adjugate p.1 p.2))
    (specialRelations k c).2.2

/-- These specific coordinate maps uniquely determine the special linear group structure.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
Proof: on a coordinate x_ij both associativity composites are the same double sum;
the two unit composites sum Kronecker deltas; both inverse composites are delta_ij by
the two adjugate identities and det X=1. Quotient maps are determined by the coordinates.
The affine tensor-product correspondence turns these equalities into the group diagrams.
All three data fields are fixed, so proof irrelevance gives uniqueness (steps 5 and 8). -/
theorem specialGroup_existsUnique :
    ∃! h : GrpObj (specialLinear k c),
      h.one = StandardGroupSchemes.identitySection k (specialCounit k c) ∧
      h.mul = StandardGroupSchemes.multiplication k (specialComul k c) ∧
      h.inv = StandardGroupSchemes.map k (specialAntipode k c) := by
  sorry

/-- The uniquely specified group law; no unspecified group structure is chosen.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
-/
noncomputable instance specialGroup : GrpObj (specialLinear k c) :=
  (specialGroup_existsUnique k c).exists.choose

/-- The quotient has determinant 1, so its determinant is a unit.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
Proof: the quotient kills det X - 1, so the image of det X is 1. Thus it is a unit
(step 7, using the quotient-algebra definition). -/
theorem specialDet_isUnit :
    IsUnit ((Ideal.Quotient.mkₐ k (specialIdeal k c))
      (Matrix.GeneralLinearGroup.genericMatrix (Index.{u} c) k).det) := by
  sorry

/-- The canonical surjection from localized GL coordinates to determinant-one coordinates.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
-/
noncomputable def specialQuotient :
    Matrix.GeneralLinearGroup.CoordinateRing (Index.{u} c) k →ₐ[k] SpecialAlgebra k c :=
  IsLocalization.Away.liftAlgHom
    (Matrix.GeneralLinearGroup.genericMatrix (Index.{u} c) k).det
    (f := Ideal.Quotient.mkₐ k (specialIdeal k c)) (specialDet_isUnit k c)

/-- The inclusion SL_c into the existing GL_c, induced by the specified quotient map.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
-/
noncomputable def inclusion : specialLinear k c ⟶ GeneralLinearGroup (Index.{u} c) k :=
  StandardGroupSchemes.map k
    (A := Matrix.GeneralLinearGroup.CoordinateRing (Index.{u} c) k)
    (B := SpecialAlgebra k c) (specialQuotient k c)

/-- The quotient inclusion is a closed subgroup scheme, with the stated value on det inverse.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
Proof: the localization extension fixes every polynomial residue and sends det inverse to 1.
Every residue class has a polynomial representative, so this map is surjective; Spec of it
is a closed immersion. Multiplication, identity and inverse commute on every coordinate,
so it is a group homomorphism. The immersion is a monomorphism, hence injective on points
(steps 7 and 8). -/
theorem inclusion_specification :
    IsClosedSubgroupScheme (inclusion k c) ∧
    Function.Surjective (specialQuotient k c) ∧
    specialQuotient k c (IsLocalization.Away.invSelf
      (Matrix.GeneralLinearGroup.genericMatrix (Index.{u} c) k).det) = 1 ∧
    (∀ i j, specialQuotient k c (Matrix.GeneralLinearGroup.coord (Index.{u} c) k i j) =
      specialMatrix k c i j) := by
  sorry

/-- The Laurent substitution t maps to the determinant of the universal invertible matrix.
It fixes k, as required for a k-algebra homomorphism.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
Proof: Laurent evaluation sends a constant to its coefficient (step 6). -/
theorem determinant_commutes (a : k) :
    LaurentPolynomial.eval₂ (algebraMap k _)
      (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.genericUnit (Index.{u} c) k))
      (algebraMap k (LaurentPolynomial k) a) =
        algebraMap k (Matrix.GeneralLinearGroup.CoordinateRing (Index.{u} c) k) a := by
  sorry

/-- The actual coefficient-fixing algebra map k[t,t⁻¹] to k[GL_c], t mapping to det X.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
-/
noncomputable def determinantCoordinates : LaurentPolynomial k →ₐ[k]
    Matrix.GeneralLinearGroup.CoordinateRing (Index.{u} c) k :=
  { LaurentPolynomial.eval₂ (algebraMap k _)
      (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.genericUnit (Index.{u} c) k)) with
    commutes' := determinant_commutes k c }

/-- The determinant morphism into the recorded multiplicative group scheme.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
-/
noncomputable def determinant : GeneralLinearGroup (Index.{u} c) k ⟶
    StandardGroupSchemes.multiplicative k :=
  StandardGroupSchemes.map k (A := LaurentPolynomial k)
    (B := Matrix.GeneralLinearGroup.CoordinateRing (Index.{u} c) k)
    (determinantCoordinates k c)

/-- The determinant is a group homomorphism with the specified coordinate value.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
Proof: det(X_L X_R)=det(X_L)det(X_R), det I=1 and det(X inverse)=(det X) inverse.
Thus the Laurent generator respects all structure maps, hence so do all Laurent polynomials;
faithful Spec gives compatibility with multiplication (steps 1 and 6). -/
theorem determinant_specification :
    IsMonHom (determinant k c) ∧
    determinantCoordinates k c (LaurentPolynomial.T 1) =
      algebraMap (MvPolynomial (Index.{u} c × Index.{u} c) k)
        (Matrix.GeneralLinearGroup.CoordinateRing (Index.{u} c) k)
        (Matrix.GeneralLinearGroup.genericMatrix (Index.{u} c) k).det := by
  sorry

/-- The antipode's adjugate formula, with the exact transposed signed minor for c = d+1.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
Proof: the generic matrix inverse is det inverse times its adjugate, by both adjugate
identities (step 2). The adjugate entry is (-1)^(i+j) times the minor deleting row j
and column i; for d=0 the determinant of this empty minor is 1. -/
theorem generalAntipode_minor (d : ℕ) (i j : Fin (d + 1)) :
    Matrix.GeneralLinearGroup.antipodeAlgHom (Index.{u} (d + 1)) k
      (Matrix.GeneralLinearGroup.coord (Index.{u} (d + 1)) k ⟨i⟩ ⟨j⟩) =
    algebraMap (MvPolynomial (Index.{u} (d + 1) × Index.{u} (d + 1)) k) _
      ((-1) ^ (i.val + j.val) *
        ((Matrix.GeneralLinearGroup.genericMatrix (Index.{u} (d + 1)) k).submatrix
          (fun r : Fin d ↦ ⟨j.succAbove r⟩) (fun r : Fin d ↦ ⟨i.succAbove r⟩)).det) *
      IsLocalization.Away.invSelf
        (Matrix.GeneralLinearGroup.genericMatrix (Index.{u} (d + 1)) k).det := by
  sorry

variable (R : Type u) [CommRing R] [Algebra k R]

/-- The canonical group identification of SL points with determinant-one matrices.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
Proof: polynomial evaluation at a matrix factors through the quotient exactly when its
determinant is 1. The affine spectrum correspondence gives a bijection, and the specified
comultiplication gives matrix multiplication. Compatibility with the inclusion fixes the
bijection uniquely because the map from special to general linear matrices is injective.
This is steps 3, 7 and 8, with no reducedness assumption on R. -/
theorem specialPoints_existsUnique :
    ∃! e : (StandardGroupSchemes.affine k R ⟶ specialLinear k c) ≃*
      Matrix.SpecialLinearGroup (Index.{u} c) R,
      ∀ x, GeneralLinearGroup.homMulEquiv (Index.{u} c) k R (x ≫ inclusion k c) =
        Matrix.SpecialLinearGroup.toGL (e x) := by
  sorry

/-- The uniquely specified point identification, using the existing matrix group.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
-/
noncomputable def specialPoints :
    (StandardGroupSchemes.affine k R ⟶ specialLinear k c) ≃*
      Matrix.SpecialLinearGroup (Index.{u} c) R :=
  (specialPoints_existsUnique k c R).exists.choose

/-- The determinant-one point identification is natural in every k-algebra, including the zero
ring and nonreduced algebras.
Source: current blueprint, def-sc-general-linear-group (blueprint: def-sc-general-linear-group).
Proof: precomposition by Spec of an algebra map applies that map to every coordinate entry.
Polynomial evaluation commutes with it, and the quotient relation remains det=1; the
inclusion compatibility determines the point identification (steps 3 and 7). -/
theorem specialPoints_natural (S : Type u) [CommRing S] [Algebra k S] (φ : R →ₐ[k] S)
    (x : StandardGroupSchemes.affine k R ⟶ specialLinear k c) :
    specialPoints k c S (StandardGroupSchemes.map k φ ≫ x) =
      Matrix.SpecialLinearGroup.map φ.toRingHom (specialPoints k c R x) := by
  sorry

end AlgebraicGeometry.LinearGroupSchemes
