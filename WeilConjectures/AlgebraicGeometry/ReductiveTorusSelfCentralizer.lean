/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # A geometrically maximal torus is its own scheme-theoretic centralizer

Source: Milne, Algebraic Groups (2017), Proposition 17.61(a), p.372, and
Proposition 1.92, pp.33--34 (blueprint: lem-sfb-reductive-torus-self-centralizer).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ReductiveTorusCentralizer

/-- A geometrically maximal torus in a reductive group represents its centralizer
on every commutative algebra, including nonreduced algebras.
Source: Milne, Proposition 17.61(a), p.372; Proposition 1.92, pp.33--34
(blueprint: lem-sfb-reductive-torus-self-centralizer).

Proof: (1) Write G = Spec R and T = Spec D. The diagonal of G is closed since
R tensor R -> R is surjective. Apply lem-sfb-constant-source-closed-factorization-locus
with Y = T, S = G, X = G x G, W the diagonal, and (t,g) |-> (t,gtg^-1).
This constructs the closed centralizer subgroup and identifies its functor using the
universal T-point over A tensor D. The base-change clause identifies its field extensions.
(2) Extend to the algebraic closure. Smoothness survives base change
(lem-pc-proper-base-change). By lem-sfb-torus-centralizer-smooth-connected the
centralizer is smooth and connected, hence reduced (sbc-lem-smooth-geometrically-reduced).
By lem-sfb-maximal-torus-centralizer-borel it lies in every Borel containing T.
(3) Its connected image lies in the identity component of their intersection and, by
reducedness, factors through its reduction. By lem-sfb-chevalley-borel-intersection,
this is the product of the unipotent radical with T. Reductivity kills the radical;
the reverse inclusion follows from commutativity of a split torus. Thus the closed
subgroup schemes agree over the algebraic closure.
(4) Descend equality of their defining ideals: for any k-vector space V the map
V -> V tensor kbar is injective, as seen by extending a nonzero vector to a basis
and taking its coefficient functional. Apply this to each quotient by a defining
ideal. The resulting equality of closed subschemes gives the displayed equality
on every test algebra, and the given closed inclusion of T is its representation. -/
theorem reductive_torus_self_centralizer {k : Type u} [Field k]
    {T G : Grp (Over (Spec (.of k)))} (i : T ⟶ G)
    (hG : IsReductive G) (hT : SolvableGroupStructure.IsAlgebraic T)
    (hi : IsClosedSubgroupScheme i.hom.hom) (ht : MultiplicativeType.IsTorus T)
    (hmax : IsMaximalTorus
      ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).map i)) :
    ∀ (A : Type u) [CommRing A] [Algebra k A],
      centralizerPoints i A =
        Set.range (fun t : StandardGroupSchemes.affine k A ⟶ T.X ↦ t ≫ i.hom.hom) := by
  sorry

end AlgebraicGeometry.ReductiveTorusCentralizer
