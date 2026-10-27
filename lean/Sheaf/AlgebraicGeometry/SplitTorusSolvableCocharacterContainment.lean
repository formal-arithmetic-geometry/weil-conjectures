module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.AdjointCharacterWeightVectors
public import Sheaf.AlgebraicGeometry.CocharacterLimitSmoothStructure
import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality

/-! # A regular cocharacter whose limit subgroup contains a solvable subgroup

Source: Milne, Algebraic Groups (2017), Proposition 21.29, Theorem 21.32 and
Corollary 21.33, pp.433--435
(blueprint: lem-sfb-split-torus-solvable-cocharacter-containment).

The ground field is arbitrary. Regularity uses actual character weights on the
identity tangent space, and containment is tested on all commutative algebras.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- A smooth connected solvable closed subgroup through a split maximal torus
lies in the limit subgroup of a regular ground-field cocharacter. If there are
no nonzero adjoint character weights, the chosen cocharacter is trivial.
Source: Milne, Proposition 21.29, Theorem 21.32 and Corollary 21.33, pp.433--435
(blueprint: lem-sfb-split-torus-solvable-cocharacter-containment).

Proof plan, following the six steps of the node:
1. Extend to K = algebraic closure of k. The field-extension assertions of
lem-sfb-solvable-normal-subgroup-products preserve smoothness, connectedness and
solvability of V. Reductivity is geometric, and lem-sfb-maximal-torus-field-extension
makes T_K maximal in G_K.
2. Choose a smooth connected solvable overgroup B of V_K of greatest dimension.
The dimensions are nonnegative integers bounded by dim G_K. A proper smooth
connected overgroup has larger dimension by lem-sfb-solvable-normal-subgroup-products,
so B is a Borel containing T_K.
3. Apply lem-sfb-regular-cocharacter-borel-description to (G_K,T_K,B). It gives a
regular mu with B = P_mu. In the empty-root case choose mu = 0 and P_0 = G_K = T_K.
4. By lem-sfb-multiplicative-character-antiduality and its scalar-extension clause,
Hom(G_m,T) is the integral dual of the split character lattice over both k and K.
Thus mu descends to a k-cocharacter lam, with lam = 0 when mu = 0.
5. By lem-sfb-relative-tangent-weight-base-change, geometric character-weight spaces
are K tensor the k-weight spaces. Field extension detects their nonzeroness, and
character antiduality preserves the pairings. Hence every nonzero adjoint weight
pairs with lam to a nonzero integer. The universal dual-number equations defining
weightVectors express precisely these character spaces over k.
6. By lem-sfb-reductive-cocharacter-parabolic-geometry, P_lam is closed and commutes
with field extension. The geometric inclusion V_K ⊆ P_mu descends: if G = Spec R,
V = Spec(R/I), and P_lam = Spec(R/J), it says J maps to zero in (R/I) tensor K.
The map R/I → (R/I) tensor K is injective, so J ⊆ I. Thus every A-point of V lies
in P_lam, including for nonreduced A. -/
theorem splitTorus_solvable_cocharacter_containment
    {k : Type u} [Field k] (G T V : Grp (Over (Spec (.of k))))
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (i : T ⟶ G) (hT : ReductiveTorusCentralizer.IsMaximalTorus i)
    (hSplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus k r))
    (j : V ⟶ G) (hV : IsClosedSubgroupScheme j.hom.hom)
    [Smooth V.X.hom] [ConnectedSpace V.X.left]
    (hSolvable : SolvableGroupStructure.IsSolvable V)
    (tV : T ⟶ V) (hTV : tV ≫ j = i) :
    ∃ lam : Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ T,
      (∀ chi : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative k),
        chi.hom.hom ≠ 1 →
        (∃ v : GrpObj.Lie G.X, v ≠ 0 ∧ v ∈ AdjointCharacter.weightVectors i chi) →
        ∃ n : ℤ, n ≠ 0 ∧
          lam.hom.hom ≫ chi.hom.hom = (𝟙 (StandardGroupSchemes.multiplicative k)) ^ n) ∧
      (∀ (A : CommAlgCat.{u} k) (v : StandardGroupSchemes.affine k A ⟶ V.X),
        v ≫ j.hom.hom ∈ CocharacterLimit.parabolicPoints (lam ≫ i) A) ∧
      ((¬ ∃ (chi : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative k))
          (v : GrpObj.Lie G.X),
          chi.hom.hom ≠ 1 ∧ v ≠ 0 ∧ v ∈ AdjointCharacter.weightVectors i chi) →
        lam.hom.hom = 1) := by
  sorry

end AlgebraicGeometry
