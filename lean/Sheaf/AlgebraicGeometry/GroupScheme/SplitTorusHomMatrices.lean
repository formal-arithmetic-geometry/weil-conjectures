module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.Data.Matrix.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.Algebra.Polynomial.Laurent

/-! # Homomorphisms of split tori are integer matrices

Source: Milne, Algebraic Groups (2017), Theorem 12.9(a), pp.233--234, with
Proposition 12.3, Lemma 12.4 and Remark 12.6
(blueprint: lem-sfb-split-torus-hom-matrices).

We use the existing finite product of the recorded multiplicative group, including
its rank-zero tensor unit. Coordinate projections have explicit data. The theorem
states a bijection preserving entrywise addition and pointwise multiplication, and
normalizes its formula on the units of global sections of every test scheme.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.MultiplicativeType

/-- The i-th product projection to the recorded multiplicative group. Source: Milne,
Theorem 12.9(a), finite products in (76)
(blueprint: lem-sfb-split-torus-hom-matrices). -/
def splitTorusProjection (k : Type u) [Field k] :
    (n : ℕ) → Fin n → (splitTorus k n ⟶ Grp.mk (StandardGroupSchemes.multiplicative k))
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases
      (fst (Grp.mk (StandardGroupSchemes.multiplicative k)) (splitTorus k n))
      (fun j ↦ snd (Grp.mk (StandardGroupSchemes.multiplicative k)) (splitTorus k n) ≫
        splitTorusProjection k n j) i

/-- The i-th Laurent coordinate, pulled back along the actual product projection.
Source: Milne, Proposition 12.3 and Remark 12.6
(blueprint: lem-sfb-split-torus-hom-matrices). -/
def splitTorusCoordinate (k : Type u) [Field k] (n : ℕ) (i : Fin n) :
    Γ((splitTorus k n).X.left, ⊤) :=
  (splitTorusProjection k n i).hom.hom.left.appTop
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1))

/-- Integer matrices classify split-torus homomorphisms, as abelian groups, with
entrywise addition corresponding to pointwise multiplication on every scheme's points.
The point identifications are fixed by the actual Laurent coordinates; they cannot be
arbitrary bijections. Empty products use `Finset.prod` and hence equal 1.

Source: Milne, Algebraic Groups (2017), Theorem 12.9(a), pp.233--234, Proposition 12.3,
Lemma 12.4 and Remark 12.6 (blueprint: lem-sfb-split-torus-hom-matrices).

Proof:
1. From def-sc-gm-ga and def-weil-laurent-polynomial-ring, the monomials t^m form the
   Laurent basis and the Hopf maps send t^m to t^m tensor t^m, 1 and t^(-m).
   Repeatedly apply lem-weil-pbc-fibre-product-affine-spectra and the tensor-basis map
   of lem-weil-pbc-algebra-tensor-pushout-universal-property to identify the rank-n
   product with Spec k[Z^n], with basis e^v. Rank zero gives Spec k. A group morphism
   induces a k-algebra map in the opposite direction (def-weil-affine-spectrum);
   its multiplication and identity diagrams (def-sc-group-scheme) say that each
   coordinate image a satisfies Delta(a)=a tensor a and epsilon(a)=1.
2. Apply lem-sfb-group-algebra-group-like-basis. Each coordinate image is e^v for
   a unique v in Z^r: different basis vectors have different coefficients, since
   1 is not 0 in k. The images of the s generators give the s rows of a matrix.
   Multiplication, inverses and k-linearity determine the entire algebra map.
3. Conversely a matrix defines h:Z^s to Z^r by its rows and the algebra map
   sum c_v e^v to sum c_v e^(h(v)). Additivity of h verifies multiplication, unit,
   comultiplication, counit and antipode on the basis and then by linearity.
   Taking Spec gives a group morphism. The coordinate-generator calculations and
   the affine-spectrum uniqueness show that the two constructions are inverse.
4. For every k-scheme U, lem-a1-locally-ringed-space-affine-adjunction identifies
   maps into this affine target with algebra maps to R=Gamma(U,O_U). Those maps
   correspond to r units x_i and evaluate e^v as the product of x_i^(v_i).
   Composition with the coordinate map therefore gives the displayed row formula.
   This includes nonaffine, nonreduced and empty test schemes.
5. Multiplying the two monomial formulas adds their exponents in the abelian
   group R^units. Evaluating at the universal point shows the corresponding
   equality of scheme morphisms. Thus the bijection preserves the stated group
   operations; zero and negatives give the identity-valued map and inverse.
   If s=0 there are no rows and only the morphism to the trivial group. If r=0
   every row product is empty and equals 1, so only the identity section occurs. -/
theorem splitTorus_hom_matrices (k : Type u) [Field k] (r s : ℕ) :
    ∃ (p : ∀ (n : ℕ) (U : Over (Spec (.of k))),
        (U ⟶ (splitTorus k n).X) ≃* (Fin n → Γ(U.left, ⊤)ˣ))
      (e : Matrix (Fin s) (Fin r) ℤ ≃ (splitTorus k r ⟶ splitTorus k s)),
      (∀ (n : ℕ) (U : Over (Spec (.of k))) (x : U ⟶ (splitTorus k n).X) (i : Fin n),
        ↑(p n U x i) = x.left.appTop (splitTorusCoordinate k n i)) ∧
      (∀ (M : Matrix (Fin s) (Fin r) ℤ) (U : Over (Spec (.of k)))
        (x : U ⟶ (splitTorus k r).X) (j : Fin s),
        p s U (x ≫ (e M).hom.hom) j = ∏ i : Fin r, p r U x i ^ M j i) ∧
      (∀ M N : Matrix (Fin s) (Fin r) ℤ,
        (e (M + N)).hom.hom = (e M).hom.hom * (e N).hom.hom) := by
  sorry

end AlgebraicGeometry.MultiplicativeType
