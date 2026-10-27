module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Localization.Defs
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Relative block Gauss chart

Source: Milne, Algebraic Groups (2017), §23h, (152)–(153), pp.510–511;
the arbitrary-base coordinate argument in the DAG.
(blueprint: lem-sfb-relative-block-gauss-chart)

The coordinate ideals and localization are actual constructions. Products are products
in the category of schemes over Spec A, hence fibre products over Spec A. The theorem
characterizes the isomorphism by multiplication on every algebra, rather than on fields.
Compatibility of the inverse is recorded on all algebra-valued points, also when the
base ring changes. These point identities express the corresponding scheme identities.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RelativeBlockGauss

/-- The basis indices of the sum of the blocks, lifted to the base-ring universe.
Source: Milne §23h and the arbitrary-base coordinate argument
(blueprint: lem-sfb-relative-block-gauss-chart). -/
abbrev Index {s : ℕ} (r : Fin s → ℕ) := Σ i : Fin s, ULift.{u} (Fin (r i))

variable {s : ℕ} (A : Type u) [CommRing A] (r : Fin s → ℕ)

/-- The existing coordinate algebra A[x_ab, det(x)⁻¹].
Source: Milne §23h and the arbitrary-base coordinate argument
(blueprint: lem-sfb-relative-block-gauss-chart). -/
abbrev Coordinates := Matrix.GeneralLinearGroup.CoordinateRing (Index.{u} r) A

/-- The determinant of the first j+1 blocks, with the empty determinant convention.
Source: Milne §23h and the arbitrary-base coordinate argument
(blueprint: lem-sfb-relative-block-gauss-chart). -/
noncomputable def leadingMinor {B : Type u} [CommRing B]
    (g : Matrix (Index.{u} r) (Index.{u} r) B) (j : Fin s) : B :=
  (g.toSquareBlockProp fun a ↦ a.1 ≤ j).det

/-- The product of all leading block minors in the GL coordinate algebra.
Source: Milne §23h and the arbitrary-base coordinate argument
(blueprint: lem-sfb-relative-block-gauss-chart). -/
noncomputable def minors : Coordinates A r :=
  ∏ j : Fin s, leadingMinor r
    (Matrix.GeneralLinearGroup.genericUnit (Index.{u} r) A).val j

/-- The constraints for lower (t=0), diagonal (t=1), and upper (t=2) factors.
Source: Milne §23h and the arbitrary-base coordinate argument
(blueprint: lem-sfb-relative-block-gauss-chart). -/
def constrained (t : Fin 3) (i j : Index.{u} r) : Prop :=
  if t = 0 then i.1 ≤ j.1 else if t = 1 then i.1 ≠ j.1 else j.1 ≤ i.1

/-- The actual defining ideal: prescribed entries equal the corresponding identity entries.
Source: Milne §23h and the arbitrary-base coordinate argument
(blueprint: lem-sfb-relative-block-gauss-chart). -/
noncomputable def factorIdeal (t : Fin 3) : Ideal (Coordinates A r) :=
  Ideal.span {x | ∃ i j : Index.{u} r, constrained r t i j ∧
    x = Matrix.GeneralLinearGroup.coord (Index.{u} r) A i j -
      (1 : Matrix (Index.{u} r) (Index.{u} r) (Coordinates A r)) i j}

/-- The three closed subschemes of GL, formed by quotienting its coordinate ring.
Source: Milne §23h and the arbitrary-base coordinate argument
(blueprint: lem-sfb-relative-block-gauss-chart). -/
noncomputable def factor (t : Fin 3) : Over (Spec (.of A)) :=
  (algSpec (.of A)).obj (op (CommAlgCat.of A (Coordinates A r ⧸ factorIdeal A r t)))

/-- The closed-subscheme inclusion, induced by the actual quotient homomorphism.
Source: Milne §23h and the arbitrary-base coordinate argument
(blueprint: lem-sfb-relative-block-gauss-chart). -/
noncomputable def factorι (t : Fin 3) :
    factor A r t ⟶ GeneralLinearGroup (Index.{u} r) A :=
  (algSpec (.of A)).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ A (factorIdeal A r t))).op

/-- The principal open, as the spectrum of the localization at the product of minors.
Source: Milne §23h and the arbitrary-base coordinate argument
(blueprint: lem-sfb-relative-block-gauss-chart). -/
noncomputable def cell : Over (Spec (.of A)) :=
  (algSpec (.of A)).obj (op (CommAlgCat.of A (Localization.Away (minors A r))))

/-- The principal-open inclusion, induced by localization of the GL coordinate ring.
Source: Milne §23h and the arbitrary-base coordinate argument
(blueprint: lem-sfb-relative-block-gauss-chart). -/
noncomputable def cellι : cell A r ⟶ GeneralLinearGroup (Index.{u} r) A :=
  (algSpec (.of A)).map
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom A (Coordinates A r)
      (Localization.Away (minors A r)))).op

/-- L ×_A D ×_A U, using the categorical product of the three displayed factors.
Source: Milne §23h and the arbitrary-base coordinate argument
(blueprint: lem-sfb-relative-block-gauss-chart). -/
noncomputable def factors : Over (Spec (.of A)) :=
  ∏ᶜ fun t : Fin 3 ↦ factor A r t

/-- The matrix attached to a factor-valued point by the existing GL point equivalence.
Source: Milne §23h and the arbitrary-base coordinate argument
(blueprint: lem-sfb-relative-block-gauss-chart). -/
noncomputable def factorPoint (B : Type u) [CommRing B] [Algebra A B] (t : Fin 3)
    (x : (Spec (.of B)).asOver (Spec (.of A)) ⟶ factor A r t) :
    Matrix.GeneralLinearGroup (Index.{u} r) B :=
  GeneralLinearGroup.homMulEquiv (Index.{u} r) A B (x ≫ factorι A r t)

/-- The invertible matrix attached to a point of the principal open.
Source: Milne §23h and the arbitrary-base coordinate argument
(blueprint: lem-sfb-relative-block-gauss-chart). -/
noncomputable def cellPoint (B : Type u) [CommRing B] [Algebra A B]
    (x : (Spec (.of B)).asOver (Spec (.of A)) ⟶ cell A r) :
    Matrix.GeneralLinearGroup (Index.{u} r) B :=
  GeneralLinearGroup.homMulEquiv (Index.{u} r) A B (x ≫ cellι A r)

/-- The t-th factor of a product-valued point, as an invertible matrix.
Source: Milne §23h and the arbitrary-base coordinate argument
(blueprint: lem-sfb-relative-block-gauss-chart). -/
noncomputable def productPoint (B : Type u) [CommRing B] [Algebra A B]
    (x : (Spec (.of B)).asOver (Spec (.of A)) ⟶ factors A r) (t : Fin 3) :
    Matrix.GeneralLinearGroup (Index.{u} r) B :=
  factorPoint A r B t (x ≫ Pi.π (fun t : Fin 3 ↦ factor A r t) t)

/-- The characterization that fixes the forward isomorphism to be matrix multiplication.
Source: Milne §23h and the arbitrary-base coordinate argument
(blueprint: lem-sfb-relative-block-gauss-chart). -/
def IsMultiplication (e : factors A r ≅ cell A r) : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra A B]
    (x : (Spec (.of B)).asOver (Spec (.of A)) ⟶ factors A r),
    cellPoint A r B (x ≫ e.hom) =
      productPoint A r B x 0 * productPoint A r B x 1 * productPoint A r B x 2

/-- The inverse Gauss factors, retaining their order lower, diagonal, upper.
Source: Milne §23h and the arbitrary-base coordinate argument
(blueprint: lem-sfb-relative-block-gauss-chart). -/
noncomputable def inverseFactor (e : factors A r ≅ cell A r)
    (B : Type u) [CommRing B] [Algebra A B]
    (y : (Spec (.of B)).asOver (Spec (.of A)) ⟶ cell A r) (t : Fin 3) :
    Matrix.GeneralLinearGroup (Index.{u} r) B :=
  productPoint A r B (y ≫ e.inv) t

/-- The standard product of the general linear groups of the individual blocks.
Source: Milne §23h and the arbitrary-base coordinate argument
(blueprint: lem-sfb-relative-block-gauss-chart). -/
noncomputable def diagonalProduct : Over (Spec (.of A)) :=
  ∏ᶜ fun i : Fin s ↦ GeneralLinearGroup (ULift.{u} (Fin (r i))) A

/-- Block diagonal embedding on all algebra-valued points, using the existing block matrix.
Source: Milne §23h and the arbitrary-base coordinate argument
(blueprint: lem-sfb-relative-block-gauss-chart). -/
noncomputable def diagonalPoint (B : Type u) [CommRing B] [Algebra A B]
    (x : (Spec (.of B)).asOver (Spec (.of A)) ⟶ diagonalProduct A r) :
    Matrix (Index.{u} r) (Index.{u} r) B :=
  Matrix.blockDiagonal' fun i ↦
    (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin (r i))) A B
      (x ≫ Pi.π (fun i : Fin s ↦ GeneralLinearGroup (ULift.{u} (Fin (r i))) A) i)).val

/-- Block Gauss multiplication is an isomorphism over every commutative base ring.
Source: Milne §23h, (152)–(153), pp.510–511, generalized by the DAG's coordinate proof
(blueprint: lem-sfb-relative-block-gauss-chart).

Proof (the eight steps of the node).
1. For no blocks all coordinate rings are A. Otherwise strictly block triangular N
   satisfies N^s=0, giving the finite geometric inverse of I+N. The quotient coordinates
   therefore give precisely lower and upper unitriangular matrices, with determinant one.
   Adjugates identify the diagonal factors with invertible matrices on each block.
2. Affine fibre products are spectra of tensor products. Polynomial evaluation and
   localization identify the cell's points over every algebra with matrices whose leading
   minors are units; a product is a unit exactly when each factor is a unit.
3. The leading minors of ldu are the products of the diagonal-block determinants.
   Thus polynomial multiplication extends across localization to a morphism into the cell.
4. Inductively split off the first invertible block P, replace the remaining matrix by
   W-TP⁻¹Q, and use the Schur determinant identity to preserve invertible leading minors.
   The Schur factorization and induction construct all three factors over every algebra.
5. Comparing the four blocks of a product forces P, P⁻¹Q, TP⁻¹ and the Schur complement;
   induction gives uniqueness. Ring homomorphisms preserve these unique factors.
6. Apply existence to the universal matrix over the localized coordinate ring, obtaining
   a regular inverse. Uniqueness on the universal triple proves both inverse identities.
7. Tensoring coordinates along any base ring map gives the same polynomial and localized
   algebras. Multiplication and its unique inverse therefore commute with arbitrary base
   change; the displayed equal-matrix test records this on every common test algebra.
8. Block diagonal conjugation preserves all constraints and leading minors. Associativity
   and uniqueness give conjugation of each inverse factor. Universal coordinate rings turn
   the point identities into identities of scheme morphisms, including nonreduced bases.
-/
theorem relative_block_gauss_chart (hr : ∀ i : Fin s, 0 < r i) :
    (∀ t : Fin 3, IsClosedImmersion (factorι A r t).left) ∧
    IsOpenImmersion (cellι A r).left ∧
    Set.range (cellι A r).left =
      (PrimeSpectrum.basicOpen (minors A r) : Set (PrimeSpectrum (Coordinates A r))) ∧
    (∃ d : factor A r 1 ≅ diagonalProduct A r,
      ∀ (B : Type u) [CommRing B] [Algebra A B]
        (x : (Spec (.of B)).asOver (Spec (.of A)) ⟶ factor A r 1),
        (factorPoint A r B 1 x).val = diagonalPoint A r B (x ≫ d.hom)) ∧
    (∀ (B : Type u) [CommRing B] [Algebra A B]
      (g : Matrix.GeneralLinearGroup (Index.{u} r) B),
      (∃ y : (Spec (.of B)).asOver (Spec (.of A)) ⟶ cell A r,
        cellPoint A r B y = g) ↔ ∀ j : Fin s, IsUnit (leadingMinor r g.val j)) ∧
    (∃ e : factors A r ≅ cell A r, IsMultiplication A r e ∧
      (∀ (B : Type u) [CommRing B] [Algebra A B]
        (y : (Spec (.of B)).asOver (Spec (.of A)) ⟶ cell A r),
        ∃! x : (Spec (.of B)).asOver (Spec (.of A)) ⟶ factors A r,
          productPoint A r B x 0 * productPoint A r B x 1 * productPoint A r B x 2 =
            cellPoint A r B y) ∧
      (∀ (B C : Type u) [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
        (ψ : B →ₐ[A] C) (y : (Spec (.of B)).asOver (Spec (.of A)) ⟶ cell A r)
        (t : Fin 3),
        inverseFactor A r e C
            ((Spec.map (CommRingCat.ofHom ψ.toRingHom)).asOver (Spec (.of A)) ≫ y) t =
          Matrix.GeneralLinearGroup.map ψ.toRingHom (inverseFactor A r e B y t)) ∧
      (∀ (A' : Type u) [CommRing A'] (e' : factors A' r ≅ cell A' r),
        IsMultiplication A' r e' →
        ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra A' B]
          (y : (Spec (.of B)).asOver (Spec (.of A)) ⟶ cell A r)
          (z : (Spec (.of B)).asOver (Spec (.of A')) ⟶ cell A' r),
          cellPoint A r B y = cellPoint A' r B z →
          ∀ t : Fin 3, inverseFactor A r e B y t = inverseFactor A' r e' B z t) ∧
      (∀ (B : Type u) [CommRing B] [Algebra A B]
        (h : (Spec (.of B)).asOver (Spec (.of A)) ⟶ factor A r 1)
        (y z : (Spec (.of B)).asOver (Spec (.of A)) ⟶ cell A r),
        cellPoint A r B z = factorPoint A r B 1 h * cellPoint A r B y *
            (factorPoint A r B 1 h)⁻¹ →
        ∀ t : Fin 3, inverseFactor A r e B z t =
          factorPoint A r B 1 h * inverseFactor A r e B y t *
            (factorPoint A r B 1 h)⁻¹)) ∧
    (s = 0 → minors A r = 1 ∧
      (∀ t : Fin 3, Nonempty (factor A r t ≅ Over.mk (𝟙 (Spec (.of A))))) ∧
      Nonempty (cell A r ≅ Over.mk (𝟙 (Spec (.of A))))) := by
  sorry

end AlgebraicGeometry.RelativeBlockGauss
