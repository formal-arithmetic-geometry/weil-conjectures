module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Barsotti--Chevalley decomposition over an algebraically closed field

Source: Milne, Algebraic Groups (2017), Theorem 8.27 and Note 8.30, pp.154--155;
Theorem 5.14 and Propositions 5.24--5.25, pp.102,104--105.
(blueprint: lem-sfb-barsotti-chevalley-decomposition)
-/

@[expose] public section

universe u

open CategoryTheory Limits CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A smooth connected separated group scheme of finite type over an algebraically
closed field is an extension of an abelian variety by a smooth connected affine
closed normal subgroup of finite type. The cartesian square is the scheme-theoretic
kernel identification, and local surjectivity is for the big fppf topology.

Source: Milne, Algebraic Groups (2017), Theorem 8.27 and Note 8.30, pp.154--155;
quotient theory in Theorem 5.14 and Propositions 5.24--5.25, pp.102,104--105.
(blueprint: lem-sfb-barsotti-chevalley-decomposition)

Proof:
1. By lem-sfb-affine-normal-subgroup-products, dimensions of smooth connected affine
   closed normal subgroups are bounded by dim H. The identity subgroup exists, so
   choose one L of greatest dimension.
2. For any other such subgroup M, the same lemma constructs LM. A strict inclusion
   L into LM would increase dimension, contradicting the choice. Thus M lies in L.
3. Apply lem-sfb-smooth-affine-normal-quotient-lifts to obtain a smooth connected
   separated finite-type quotient Q and a smooth surjective finitely presented
   homomorphism p with scheme-theoretic kernel L.
4. A smooth connected affine closed normal subgroup S of Q has inverse image P
   of the same kind in H. Maximality gives P = L. Pulling p back along any T-point
   of S yields a flat surjective finitely presented cover on which that point is
   the identity. This is an fpqc cover (def-weil-pbc-fpqc-covering), so uniqueness
   in lem-weil-pbc-fpqc-representable-descent makes the original point the identity.
   Apply this to the identity map of S to conclude that S is the trivial group.
5. By lem-sfb-pseudoabelian-proper-algclosed, Q is proper. Together with smoothness
   and connectedness this is IsAbelianVariety Q (def-sc-abelian-variety). Set C = Q.
6. For every T-point of C, the pullback of p is a flat surjective locally finitely
   presented morphism and hence an fppf cover. Its map to H lifts the given point.
   Thus p is fppf locally surjective; the kernel square is the one from step 3.
No commutativity or positive-dimension hypothesis is used. -/
theorem exists_barsotti_chevalley_decomposition
    (k : Type u) [Field k] [IsAlgClosed k]
    (H : Over (Spec (.of k))) [GrpObj H]
    [Smooth H.hom] [ConnectedSpace H.left] [IsSeparated H.hom]
    [LocallyOfFiniteType H.hom] [QuasiCompact H.hom] :
    ∃ (L C : Grp (Over (Spec (.of k)))) (a : L.X ⟶ H) (p : H ⟶ C.X),
      Smooth L.X.hom ∧ ConnectedSpace L.X.left ∧ IsAffine L.X.left ∧
      LocallyOfFiniteType L.X.hom ∧ QuasiCompact L.X.hom ∧
      IsClosedSubgroupScheme a ∧ IsNormalSubgroupScheme a ∧
      IsAbelianVariety C.X ∧ IsMonHom p ∧
      IsPullback a (toUnit L.X) p η[C.X] ∧
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of k)))
        (yoneda.map p) := by
  sorry

end AlgebraicGeometry
