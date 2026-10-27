module

public import Sheaf.AlgebraicGeometry.DiagonalizableGroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Algebra.CharP.Defs

import Mathlib.GroupTheory.FiniteAbelian.Basic
import Sheaf.AlgebraicGeometry.StandardGroupSchemes
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.AdjoinRoot

/-! # Prime-to-characteristic torsion in a smooth diagonalizable group

Source: Milne, Algebraic Groups (2017), Proposition 12.3 and Remark 12.5, pp.231--232;
Theorems 12.32--12.33, pp.242--243; Proposition 15.3, p.303
(blueprint: lem-sfb-smooth-diagonal-prime-to-characteristic-torsion-density).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

/-- The prime-to-characteristic torsion kernels are finite split schemes of positive
prime-to-characteristic order, and jointly detect closed subschemes and regular functions.
`ringExpChar F` is 1 in characteristic zero and the characteristic otherwise.
The displayed isomorphism uses the canonical Hopf structure on F[M]. No connectedness
assumption is made. The finite coproduct is in F-schemes, so every summand is Spec F.

Source: Milne, Algebraic Groups (2017), Proposition 12.3 and Remark 12.5, pp.231--232;
Theorems 12.32--12.33, pp.242--243; Proposition 15.3, p.303
(blueprint: lem-sfb-smooth-diagonal-prime-to-characteristic-torsion-density).

Proof:
1. By lem-sbc-finitely-generated-abelian-group-structure, decompose M as a free
   group plus finite cyclic factors. By lem-sfb-diagonalizable-group-geometric-criteria,
   D is G_m^r times the mu_(d_i); smoothness forces every d_i prime to p.
   Put d equal to their product (1 for the empty product).
2. On every F-algebra the n-torsion kernel is mu_n^r times mu_(gcd(d_i,n)).
   Bezout identifies the ideals (T^n-1,T^(d_i)-1) and (T^gcd(d_i,n)-1), including
   over rings with nilpotents; this is an equality of subgroup schemes.
3. For a prime to p, lem-sfb-split-binomial-root-torsor splits T^a-1 into distinct
   linear factors. By lem-pc-crt-ideal-quotient-product and
   lem-weil-pbc-finite-affine-coproduct-spectrum, mu_a is a disjoint union of a
   copies of Spec F. Use lem-weil-pbc-fibre-product-affine-spectra and
   lem-weil-pbc-algebra-tensor-pushout-universal-property to take their products.
   Thus c_n = n^r times the product of gcd(d_i,n), positive and coprime to p.
4. Write B for the finite-factor algebra and L = B[t_1^+-1,...,t_r^+-1].
   For d dividing n the restriction to D[n] is L -> L/J_n, where J_n is generated
   by t_j^n-1. By lem-weil-pbc-monic-quotient-free the quotient has B-basis
   consisting of the exponent box 0 <= v_j < n. For r=0 this is the basis {1}.
5. For a nonzero Laurent polynomial choose n=d(1+kp) larger than all widths of
   its finite support. Such n are coprime to p, including p=1. Translate its
   support into the exponent box by a monomial. The box basis shows its image
   is nonzero. Hence these restriction maps are jointly injective.
6. By def-weil-closed-immersion, a closed subscheme is Spec(L/I). Factorization
   of all torsion inclusions annihilates I under every restriction, so step 5
   gives I=0. Under the split identifications of step 3, restriction coordinates
   are values at the rational points H_n; their vanishing likewise gives zero.
   All finite factors and the zero-rank and n=1 cases are retained. -/
theorem smooth_diagonal_primeToTorsion_density
    (F : Type u) [Field F] [IsAlgClosed F]
    (D : Grp (Over (Spec (.of F))))
    [IsAffine D.X.left] [Smooth D.X.hom]
    [LocallyOfFiniteType D.X.hom] [QuasiCompact D.X.hom]
    (M : Type u) [AddCommGroup M] [AddGroup.FG M]
    (e : D ≅ diagonalizableGroup F M) :
    (∀ n : ℕ, 0 < n → n.Coprime (ringExpChar F) →
      ∃ c : ℕ, 0 < c ∧ c.Coprime (ringExpChar F) ∧
        Nat.card (𝟙_ (Over (Spec (.of F))) ⟶ torsionSubgroupScheme D.X n) = c ∧
        Nonempty (torsionSubgroupScheme D.X n ≅
          ∐ fun _ : Fin c ↦ 𝟙_ (Over (Spec (.of F))))) ∧
    (∀ (Z : Scheme.{u}) (i : Z ⟶ D.X.left), IsClosedImmersion i →
      (∀ n : ℕ, 0 < n → n.Coprime (ringExpChar F) →
        ∃ j : (torsionSubgroupScheme D.X n).left ⟶ Z,
          j ≫ i = (torsionSubgroupScheme.ι D.X n).left) → IsIso i) ∧
    (∀ f : AddMonoidAlgebra F M,
      (∀ n : ℕ, 0 < n → n.Coprime (ringExpChar F) →
        ∀ x : 𝟙_ (Over (Spec (.of F))) ⟶ torsionSubgroupScheme D.X n,
          (Spec.preimage (x.left ≫ (torsionSubgroupScheme.ι D.X n).left ≫
            e.hom.hom.hom.left)).hom f = 0) → f = 0) := by
  sorry

end AlgebraicGeometry
