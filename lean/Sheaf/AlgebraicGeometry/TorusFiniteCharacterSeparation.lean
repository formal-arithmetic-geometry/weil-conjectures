module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.Data.Set.Finite.Basic

import Mathlib.Algebra.MvPolynomial.Funext

/-! # A rational point separates finitely many torus characters

Source: Milne, Algebraic Groups (2017), Lemma 16.42, proof, printed p.339;
Theorem 12.9 and Definition 12.14, printed pp.233--236
(blueprint: lem-sfb-torus-finite-character-separation).

Characters are morphisms in the category of group schemes over k. Their values
are k-points of the recorded multiplicative group, evaluated by composition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A rational point of a split torus separates any finite set of distinct characters.
Source: Milne, Algebraic Groups (2017), Lemma 16.42, proof, printed p.339;
Theorem 12.9 and Definition 12.14, printed pp.233--236
(blueprint: lem-sfb-torus-finite-character-separation).

Proof:
1. Choose the splitting isomorphism. By lem-sfb-split-torus-hom-matrices, each
   character has a unique integer exponent vector. Distinct characters have
   distinct vectors. In rank zero there is at most one character, so use the identity.
2. The algebraically closed field is infinite: otherwise the product of X-a over
   all a in k, minus 1, is a nonconstant polynomial with no root. For each distinct
   pair of characters, clear negative exponents by a common monomial. The difference
   of the resulting distinct monomials has coefficient 1 and is nonzero in every
   characteristic (def-weil-pbc-mv-polynomial-ring).
3. Multiply these finitely many difference polynomials and all coordinate variables.
   The product is nonzero because the polynomial ring is a domain
   (lem-weil-pbc-polynomial-ring-domain); an empty pair product is 1.
4. By lem-sfb-mvpolynomial-infinite-evaluation, the product cannot evaluate to zero
   everywhere. Choose an assignment where it is nonzero. All its coordinates and
   all the pairwise difference factors are then nonzero.
5. The coordinates define a torus point. Transport it through the splitting
   isomorphism. Cancel the nonzero denominator-clearing monomials to see that every
   distinct pair of characters has unequal values. Empty and singleton sets impose
   no pairwise condition, and the identity point works in those cases. -/
theorem exists_torus_point_injOn_characters {k : Type u} [Field k] [IsAlgClosed k]
    (r : ℕ) (T : Grp (Over (Spec (.of k))))
    (hT : Nonempty (T ≅ MultiplicativeType.splitTorus k r))
    (Ω : Set (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative k))) (hΩ : Ω.Finite) :
    ∃ s : StandardGroupSchemes.affine k k ⟶ T.X,
      Set.InjOn (fun χ : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative k) ↦
        s ≫ χ.hom.hom) Ω := by
  sorry

end AlgebraicGeometry
