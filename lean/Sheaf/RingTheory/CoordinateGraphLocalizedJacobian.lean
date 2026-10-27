module

public import WeilConjectures.Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # Localized coordinate graph Jacobian

Source: Stacks 00T7(2), 02GU(8), and the prescribed-coordinate calculation in the
purity blueprint (blueprint: lem-pur-coordinate-graph-localized-jacobian).
The ordered variable set `Fin r ⊕ Fin d` is identified with `Fin (r+d)`.
The final `Unit` variable is the inverse of the graph determinant.
-/

@[expose] public section

universe u

namespace Algebra

variable {k : Type u} [Field k] {r d : ℕ}

/-- The quotient by the specified smooth equations. Source: Stacks 00T7.
(blueprint: lem-pur-coordinate-graph-localized-jacobian) -/
abbrev CoordinateGraphAlgebra (F : Fin r → MvPolynomial (Fin r ⊕ Fin d) k) :=
  MvPolynomial (Fin r ⊕ Fin d) k ⧸ Ideal.span (Set.range F)

/-- The canonical quotient map. Source: Stacks 00T7.
(blueprint: lem-pur-coordinate-graph-localized-jacobian) -/
noncomputable def coordinateGraphImage (F : Fin r → MvPolynomial (Fin r ⊕ Fin d) k) :
    MvPolynomial (Fin r ⊕ Fin d) k →ₐ[k] CoordinateGraphAlgebra F :=
  Ideal.Quotient.mkₐ k (Ideal.span (Set.range F))

/-- The graph Jacobian, with relation rows and variable columns. Source: Stacks 00T7,
explicit graph calculation. (blueprint: lem-pur-coordinate-graph-localized-jacobian) -/
noncomputable def coordinateGraphJacobian
    (F : Fin r → MvPolynomial (Fin r ⊕ Fin d) k)
    (H : Fin d → MvPolynomial (Fin r ⊕ Fin d) k) :
    Matrix (Fin r ⊕ Fin d) (Fin r ⊕ Fin d) (MvPolynomial (Fin r ⊕ Fin d) k) :=
  fun a b => MvPolynomial.pderiv b (Sum.elim F H a)

/-- The prescribed determinant in the polynomial ring. Source: Stacks 02GU(8).
(blueprint: lem-pur-coordinate-graph-localized-jacobian) -/
noncomputable def coordinateGraphDelta
    (F : Fin r → MvPolynomial (Fin r ⊕ Fin d) k)
    (H : Fin d → MvPolynomial (Fin r ⊕ Fin d) k) : MvPolynomial (Fin r ⊕ Fin d) k :=
  (coordinateGraphJacobian F H).det

/-- The Jacobian reduced to the specified residue field. Source: Stacks 00T7(2).
(blueprint: lem-pur-coordinate-graph-localized-jacobian) -/
noncomputable def coordinateGraphResidueJacobian
    (F : Fin r → MvPolynomial (Fin r ⊕ Fin d) k)
    (H : Fin d → MvPolynomial (Fin r ⊕ Fin d) k)
    (q : Ideal (CoordinateGraphAlgebra F)) [q.IsPrime] :
    Matrix (Fin r ⊕ Fin d) (Fin r ⊕ Fin d) q.ResidueField :=
  (coordinateGraphJacobian F H).map
    (fun p => algebraMap (CoordinateGraphAlgebra F) q.ResidueField (coordinateGraphImage F p))

/-- The Schur matrix in the complementary coordinates. Source: Stacks 00T7(2),
explicit block calculation. (blueprint: lem-pur-coordinate-graph-localized-jacobian) -/
noncomputable def coordinateGraphSchur
    (F : Fin r → MvPolynomial (Fin r ⊕ Fin d) k)
    (H : Fin d → MvPolynomial (Fin r ⊕ Fin d) k)
    (q : Ideal (CoordinateGraphAlgebra F)) [q.IsPrime] :
    Matrix (Fin d) (Fin d) q.ResidueField :=
  (coordinateGraphResidueJacobian F H q).toBlocks₂₂ -
    (coordinateGraphResidueJacobian F H q).toBlocks₂₁ *
      (coordinateGraphResidueJacobian F H q).toBlocks₁₁⁻¹ *
        (coordinateGraphResidueJacobian F H q).toBlocks₁₂

/-- The differential of a polynomial image in the cotangent fibre, using the canonical
commuted tensor order of base change. Source: Stacks 00T7(2).
(blueprint: lem-pur-coordinate-graph-localized-jacobian) -/
noncomputable def coordinateGraphFibreDifferential
    (F : Fin r → MvPolynomial (Fin r ⊕ Fin d) k)
    (q : Ideal (CoordinateGraphAlgebra F)) [q.IsPrime]
    (p : MvPolynomial (Fin r ⊕ Fin d) k) :
    TensorProduct (CoordinateGraphAlgebra F) q.ResidueField
      (KaehlerDifferential k (CoordinateGraphAlgebra F)) :=
  TensorProduct.tmul (CoordinateGraphAlgebra F) 1
    (KaehlerDifferential.D k (CoordinateGraphAlgebra F) (coordinateGraphImage F p))

/-- Extension of coefficients to `k[T]` and adjoining the last variable. Source: the
explicit graph presentation following Stacks 02GU(8).
(blueprint: lem-pur-coordinate-graph-localized-jacobian) -/
noncomputable def coordinateGraphLift :
    MvPolynomial (Fin r ⊕ Fin d) k →+*
      MvPolynomial ((Fin r ⊕ Fin d) ⊕ Unit) (MvPolynomial (Fin d) k) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
    (fun b => MvPolynomial.X (Sum.inl b))

/-- The ordered equations `(F,H-T,Delta*t-1)`. Source: Stacks 02GU(8), explicit
inverse-determinant presentation. (blueprint: lem-pur-coordinate-graph-localized-jacobian) -/
noncomputable def coordinateGraphRelations
    (F : Fin r → MvPolynomial (Fin r ⊕ Fin d) k)
    (H : Fin d → MvPolynomial (Fin r ⊕ Fin d) k) :
    ((Fin r ⊕ Fin d) ⊕ Unit) →
      MvPolynomial ((Fin r ⊕ Fin d) ⊕ Unit) (MvPolynomial (Fin d) k) :=
  Sum.elim
    (Sum.elim (fun a => coordinateGraphLift (F a))
      (fun j => coordinateGraphLift (H j) - MvPolynomial.C (MvPolynomial.X j)))
    (fun _ => coordinateGraphLift (coordinateGraphDelta F H) * MvPolynomial.X (Sum.inr ()) - 1)

/-- Localization at the image of the prescribed graph determinant. Source: Stacks 02GU(8).
(blueprint: lem-pur-coordinate-graph-localized-jacobian) -/
abbrev CoordinateGraphLocalization
    (F : Fin r → MvPolynomial (Fin r ⊕ Fin d) k)
    (H : Fin d → MvPolynomial (Fin r ⊕ Fin d) k) :=
  Localization.Away (coordinateGraphImage F (coordinateGraphDelta F H))

/-- The specified generator images `(a/1,delta^{-1})`. Source: the inverse-determinant
presentation following Stacks 02GU(8).
(blueprint: lem-pur-coordinate-graph-localized-jacobian) -/
noncomputable def coordinateGraphLocalizedValues
    (F : Fin r → MvPolynomial (Fin r ⊕ Fin d) k)
    (H : Fin d → MvPolynomial (Fin r ⊕ Fin d) k) :
    ((Fin r ⊕ Fin d) ⊕ Unit) → CoordinateGraphLocalization F H :=
  Sum.elim
    (fun b => algebraMap (CoordinateGraphAlgebra F) (CoordinateGraphLocalization F H)
      (coordinateGraphImage F (MvPolynomial.X b)))
    (fun _ => IsLocalization.Away.invSelf (S := CoordinateGraphLocalization F H)
      (coordinateGraphImage F (coordinateGraphDelta F H)))

/-- The canonical `k[T]` action, sending `T_j` to `h_j/1`. Source: the prescribed-coordinate
map in the purity blueprint and Stacks 02GU(8).
(blueprint: lem-pur-coordinate-graph-localized-jacobian) -/
@[instance_reducible]
noncomputable def coordinateGraphLocalizedAlgebra
    (F : Fin r → MvPolynomial (Fin r ⊕ Fin d) k)
    (H : Fin d → MvPolynomial (Fin r ⊕ Fin d) k) :
    Algebra (MvPolynomial (Fin d) k) (CoordinateGraphLocalization F H) :=
  (MvPolynomial.aeval (fun j =>
    algebraMap (CoordinateGraphAlgebra F) (CoordinateGraphLocalization F H)
      (coordinateGraphImage F (H j)))).toRingHom.toAlgebra

/-- The literal Jacobian determinant of the augmented equations over `k[T]`.
Source: the block calculation following Stacks 02GU(8).
(blueprint: lem-pur-coordinate-graph-localized-jacobian) -/
noncomputable def coordinateGraphAugmentedDeterminant
    (F : Fin r → MvPolynomial (Fin r ⊕ Fin d) k)
    (H : Fin d → MvPolynomial (Fin r ⊕ Fin d) k) :
    MvPolynomial ((Fin r ⊕ Fin d) ⊕ Unit) (MvPolynomial (Fin d) k) :=
  Matrix.det (fun a b => MvPolynomial.pderiv b (coordinateGraphRelations F H a))

/-- A prescribed cotangent-fibre basis gives the localized coordinate graph presentation.
Source: Stacks 00T7(2), 02GU(8), and the second paragraph of the purity blueprint proof
of regular-immersion linearization. (blueprint: lem-pur-coordinate-graph-localized-jacobian)

Proof plan:
1. The standard smooth Kahler basis theorem gives the complementary `da` basis; tensoring
its coordinate isomorphism and its inverse gives the residue-field basis, even for `d=0`.
2. Apply the polynomial differential formula and then the quotient derivation to obtain
`B*u+C*v=0` and `w=D*u+E*v` over the residue field.
3. The unit leading determinant makes `B` invertible (use its adjugate), so solving the
first equation and substituting into the second gives `w=(E-D*B^{-1}*C)*v`.
4. Since both differential families are bases, their transition matrix is invertible.
5. Multiply the full matrix by the determinant-one lower block elimination matrix.
Block triangular determinants and determinant multiplicativity give `det J=det B*det S`,
nonzero in the residue field. The kernel of the residue map is `q`, proving nonmembership.
6. Evaluation kills `(F,H-T,Delta*t-1)` and induces the displayed quotient map to the
localization. In the reverse direction the original quotient maps to the graph quotient;
its determinant is invertible with inverse `t`, so localization extends this map uniquely.
The composites fix all generators and the inverse determinant, hence are identities.
This is the quotient equivalence attached to the square presentation in the conclusion.
7. The augmented matrix is `[[J,0],[t*partial Delta,Delta]]`, with determinant `Delta^2`.
Its image is `delta^2`, a unit. This supplies the specified square Jacobian presentation.
All empty determinants are one; when `r=d=0` the only equation is `t-1`.
-/
theorem coordinateGraph_localized_jacobian
    (F : Fin r → MvPolynomial (Fin r ⊕ Fin d) k)
    (H : Fin d → MvPolynomial (Fin r ⊕ Fin d) k)
    (hstandard : IsUnit (coordinateGraphImage F (coordinateGraphJacobian F H).toBlocks₁₁.det))
    (q : Ideal (CoordinateGraphAlgebra F)) [q.IsPrime]
    (hind : LinearIndependent q.ResidueField (fun j => coordinateGraphFibreDifferential F q (H j)))
    (hspan : Submodule.span q.ResidueField
      (Set.range (fun j => coordinateGraphFibreDifferential F q (H j))) = ⊤)
    [aR : Algebra (MvPolynomial (Fin d) k) (CoordinateGraphLocalization F H)]
    (haR : aR = coordinateGraphLocalizedAlgebra F H) :
    coordinateGraphImage F (coordinateGraphDelta F H) ∉ q ∧
    IsUnit (coordinateGraphResidueJacobian F H q).toBlocks₁₁ ∧
    (∃ b : Module.Basis (Fin d) q.ResidueField
        (TensorProduct (CoordinateGraphAlgebra F) q.ResidueField
          (KaehlerDifferential k (CoordinateGraphAlgebra F))),
      (∀ i, b i = coordinateGraphFibreDifferential F q (MvPolynomial.X (Sum.inr i))) ∧
      (∀ j i, b.repr (coordinateGraphFibreDifferential F q (H j)) i =
        coordinateGraphSchur F H q j i)) ∧
    IsUnit (coordinateGraphSchur F H q) ∧
    (coordinateGraphResidueJacobian F H q).det =
      (coordinateGraphResidueJacobian F H q).toBlocks₁₁.det * (coordinateGraphSchur F H q).det ∧
    (coordinateGraphResidueJacobian F H q).det ≠ 0 ∧
    (∃ p : SquareJacobianPresentation (MvPolynomial (Fin d) k)
        (CoordinateGraphLocalization F H) ((Fin r ⊕ Fin d) ⊕ Unit),
      p.val = coordinateGraphLocalizedValues F H ∧
      p.relation = coordinateGraphRelations F H) ∧
    (∃ e : (MvPolynomial ((Fin r ⊕ Fin d) ⊕ Unit) (MvPolynomial (Fin d) k) ⧸
        Ideal.span (Set.range (coordinateGraphRelations F H))) ≃ₐ[MvPolynomial (Fin d) k]
        CoordinateGraphLocalization F H,
      ∀ i, e (Ideal.Quotient.mk (Ideal.span (Set.range (coordinateGraphRelations F H)))
        (MvPolynomial.X i)) = coordinateGraphLocalizedValues F H i) ∧
    coordinateGraphAugmentedDeterminant F H =
      coordinateGraphLift (coordinateGraphDelta F H) ^ 2 ∧
    MvPolynomial.aeval (coordinateGraphLocalizedValues F H)
        (coordinateGraphAugmentedDeterminant F H) =
      (algebraMap (CoordinateGraphAlgebra F) (CoordinateGraphLocalization F H)
        (coordinateGraphImage F (coordinateGraphDelta F H))) ^ 2 ∧
    IsUnit ((algebraMap (CoordinateGraphAlgebra F) (CoordinateGraphLocalization F H)
      (coordinateGraphImage F (coordinateGraphDelta F H))) ^ 2) := by
  sorry

end Algebra
