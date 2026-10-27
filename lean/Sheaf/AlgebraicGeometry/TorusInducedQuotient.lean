module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

import Sheaf.AlgebraicGeometry.FpqcAffineDescent
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover
import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Tori as quotients of induced tori

Source: Milne, Algebraic Groups (2017), Lemma 12.61, Definition 12.62 and
Proposition 12.63, printed p.251 (blueprint: lem-sfb-torus-induced-quotient).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace AlgebraicGeometry.MultiplicativeType

/-- Every torus is a scheme-surjective quotient of an affine induced torus,
with its unit-group description natural in every commutative test algebra.
The factors are commutative k-algebras satisfying IsField, so they are precisely
field extensions; separability is separability of every minimal polynomial.

Source: Milne, Algebraic Groups (2017), Lemma 12.61, Definition 12.62 and
Proposition 12.63, printed p.251 (blueprint: lem-sfb-torus-induced-quotient).

Proof plan:
1. The algebraic-closure extension is faithfully flat, hence its spectrum is
   an fpqc cover, by lem-weil-pbc-field-extension-base-change-faithfully-flat,
   lem-weil-pbc-faithfully-flat-surjective-spectrum and
   lem-weil-pbc-flat-ring-map-iff-flat-affine. The geometric split torus is
   affine and locally of finite type. Descend both properties by
   lem-weil-pbc-fpqc-descend-affine and lem-weil-pbc-fpqc-descend-locally-finite-type.
   Affine quasi-compactness then gives finite type, including rank zero.
2. By lem-sfb-multiplicative-character-antiduality and
   lem-sfb-split-torus-hom-matrices the character lattice M is Z^r with action
   through a finite Galois extension K/k with group G. Choose r coordinate
   functionals and one zero functional; put m = r+1 and N = Z[G]^m.
3. Define j(x)_(i,g) = phi_i(g^(-1)x). This is additive and G-equivariant;
   its coefficients at g=1 recover all coordinates, so j is injective.
4. By lem-sfb-induced-unit-torus-characters, Q_K has character lattice Z[G].
   Its m-fold product P is an affine torus with character lattice N, and
   full faithfulness in lem-sfb-multiplicative-character-antiduality realizes
   j as the character map of a homomorphism pi : P -> T. Its points are
   the product of the groups of units of K tensor R.
5. Over the algebraic closure, lem-sfb-relative-diagonalizable-character-duality
   makes this injective character map a faithfully flat scheme quotient.
   Thus pi is geometrically surjective on underlying topological spaces.
6. The faithfully flat field-extension projection T_kbar -> T is surjective.
   Lift each scheme point to T_kbar, lift there through pi_kbar, and project
   the resulting point to P. The base-change square proves surjectivity of pi.
7. Take L_i=K. By lem-weil-pbc-tensor-finite-product and
   lem-weil-pbc-algebra-tensor-pushout-universal-property, the product of
   L_i tensor R is the tensor of the product with R as an algebra. Units
   of a product are tuples of units. These identifications commute with
   every k-algebra map R -> R', giving the displayed naturality equation.
   The redundant factor ensures m is positive also for the trivial torus. -/
theorem torus_induced_quotient {k : Type u} [Field k]
    (T : Grp (Over (Spec (.of k)))) (hT : IsTorus T) :
    ∃ (m : ℕ), 1 ≤ m ∧
      ∃ (L : Fin m → CommAlgCat.{u} k),
        (∀ i, IsField (L i)) ∧
        (∀ i, FiniteDimensional k (L i) ∧ Algebra.IsSeparable k (L i)) ∧
        ∃ (P : Grp (Over (Spec (.of k)))), IsTorus P ∧ IsAffine P.X.left ∧
          ∃ (π : P ⟶ T), Surjective π.hom.hom.left ∧
            ∃ e : ∀ (R : CommAlgCat.{u} k),
              ((algSpec (.of k)).obj (op R) ⟶ P.X) ≃* ((∀ i, L i) ⊗[k] R)ˣ,
              ∀ (R R' : CommAlgCat.{u} k) (f : R ⟶ R')
                (p : (algSpec (.of k)).obj (op R) ⟶ P.X),
                e R' ((algSpec (.of k)).map f.op ≫ p) =
                  Units.map
                    (Algebra.TensorProduct.map (AlgHom.id k (∀ i, L i)) f.hom).toMonoidHom
                    (e R p) := by
  sorry

end AlgebraicGeometry.MultiplicativeType
