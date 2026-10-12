module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.ConstructibleSheaf.Refinement

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Finite local constancy on a stratification passes to every refinement.
Source: Stacks Project, Tags 095A, 03Q1 (3), and 03SI; compare the abelian-coefficient
argument in `WeilConjectures.ConstructibleSheaf.Refinement`.

Proof: fix i and choose k with T.stratum i contained in S.stratum k. Write
Z = T.domain i, W = S.domain k, a = T.immersion i, and b = S.immersion k.
Form P = Z times_X W with projections p to Z and q to W. The image containment makes
p surjective. It is an immersion by base change of b, hence a surjective closed
immersion and a universal homeomorphism. This avoids assuming that a factors through b,
which need not follow from containment of their underlying images.
Pull back the finite locally constant sheaf b^*F along q. A pulled-back trivializing
etale cover is still a cover and inverse image preserves constant sheaves (095A);
the stalk at each geometric point is the original stalk at its image (03Q1 (3)),
so it remains finite. Composition of inverse images and p followed by a = q followed
by b identify this sheaf with p^*(a^*F). The small etale sites of P and Z are equivalent
under p (03SI). Descend a trivializing cover and its constant-sheaf isomorphisms through
this equivalence; coverings and constant objects correspond, so a^*F is locally constant.
Every geometric point of Z lifts uniquely to P because p is a surjective closed immersion
and fields kill its defining ideal. The stalk comparison therefore also shows that all
geometric stalks of a^*F are finite. This proves the assertion for each i.
(blueprint: lem-weil-pbc-refinement-preserves-finite-lisse)
-/
theorem refinement_preserves_finite_lisse
    (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (T S : Stratification X) (hTS : T.Refines S)
    (hS : ∀ k : Fin S.n,
      IsFiniteLocallyConstantEtaleSheafOfSets
        ((etaleSetPullback (S.immersion k)).obj F)) :
    ∀ i : Fin T.n,
      IsFiniteLocallyConstantEtaleSheafOfSets
        ((etaleSetPullback (T.immersion i)).obj F) := by
  sorry

end AlgebraicGeometry.Scheme
