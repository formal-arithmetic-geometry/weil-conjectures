module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Group.Affine

import Sheaf.AlgebraicGeometry.IrreducibleProductOverField
import Sheaf.AlgebraicGeometry.GroupScheme.CentralTorusDerivedProduct
import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Centrality of normal subgroups from their neutral components

Source: Conrad, Reductive Group Schemes, proof of Theorem 3.3.4, printed p.100,
and proof of Proposition 3.3.8, printed p.102
(blueprint: lem-sfb-reductive-normal-subgroup-central-neutral-test).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- A closed normal subgroup of a reductive group is central exactly when its open
identity component is central. This component is itself closed and normal in the
ambient group. The open subscheme retains its full, possibly nonreduced structure.

Source: Conrad, Reductive Group Schemes, Theorem 3.3.4 proof, printed p.100, and
Proposition 3.3.8 proof, printed p.102; CGP, Lemma 5.3.2
(blueprint: lem-sfb-reductive-normal-subgroup-central-neutral-test).

Proof:
1. A closed subgroup N of the affine finite type G is affine of finite type, by
   def-weil-closed-immersion and def-weil-finite-type-morphism. Apply
   lem-sfb-locally-algebraic-group-identity-component to N to obtain its clopen
   geometrically irreducible open component C. Its inclusion into G is closed.
   Applying the same lemma to the connected G shows G is geometrically irreducible.
2. Normality of N defines conjugation G times C to N. Its source is irreducible by
   lem-sc-irreducible-product-over-field, so its connected image contains the identity
   and lies in C. By lem-weil-pbc-morphism-factors-through-open-subscheme it factors
   through the actual open subscheme C. Conjugation by g and its inverse therefore
   preserves C on every algebra, proving normality in G without discarding nilpotents.
3. Suppose C is central. For n in N(k), the map b_n(g) = g n g inverse n inverse
   factors through C by connectedness and the open factorization lemma. The identity
   b_n(xy) = x b_n(y) x inverse b_n(x) and centrality of C show that b_n is a
   group-scheme homomorphism to the commutative group C, on every test algebra.
4. By lem-sfb-reductive-radical-quotient the radical R is a central torus and G/R
   is semisimple. Apply lem-sfb-central-torus-semisimple-derived-product: multiplication
   R times D to G is faithfully flat, where D is the derived subgroup characterized
   by the commutators. The closed kernel of b_n (lem-sc-kernel-subgroup) contains
   every commutator, hence D. Centrality of R gives b_n restricted to R trivial too.
5. Thus b_n is trivial after multiplication R times D to G. The faithfully flat
   coordinate-ring map is injective by lem-weil-pbc-faithfully-flat-ideal-contraction
   for the zero ideal, so the two coordinate maps already agree and b_n is trivial.
6. By lem-sfb-group-neutral-component-translates, the finitely many clopen components
   of N are rational translates n_j C, as schemes. Each n_j is central by step 5,
   and C is central by hypothesis. The commutator is therefore trivial on each open
   G times n_j C, hence globally. This proves centrality on every algebra and after
   every extension, including points meeting several components. Conversely centrality
   of N restricts to C. No smoothness or reducedness of N or C is used. -/
theorem reductive_normalSubgroup_central_iff_neutralComponent_central
    {k : Type u} [Field k] [IsAlgClosed k]
    (G N : Grp (Over (Spec (.of k))))
    (hG : ReductiveTorusCentralizer.IsReductive G) (iN : N ⟶ G)
    (hclosed : IsClosedSubgroupScheme iN.hom.hom)
    (hnormal : IsNormalSubgroupScheme iN.hom.hom) :
    ∃ U : N.X.left.Opens,
      (U : Set N.X.left) = connectedComponent (GrpObj.onePoint N.X) ∧
      ∃ gC : GrpObj (Over.mk (U.ι ≫ N.X.hom)),
        @IsClosedSubgroupScheme k _ (Over.mk (U.ι ≫ N.X.hom)) G.X gC G.grp
          (Over.homMk (V := N.X) U.ι ≫ iN.hom.hom) ∧
        @IsNormalSubgroupScheme k _ (Over.mk (U.ι ≫ N.X.hom)) G.X gC G.grp
          (Over.homMk (V := N.X) U.ι ≫ iN.hom.hom) ∧
        ((∀ (A : Type u) [CommRing A] [Algebra k A]
            (n : (algSpec (.of k)).obj (.op (CommAlgCat.of k A)) ⟶ N.X),
            n ≫ iN.hom.hom ∈ ReductiveTorusCentralizer.centralizerPoints (𝟙 G) A) ↔
          ∀ (A : Type u) [CommRing A] [Algebra k A]
            (c : (algSpec (.of k)).obj (.op (CommAlgCat.of k A)) ⟶
              Over.mk (U.ι ≫ N.X.hom)),
            c ≫ Over.homMk (V := N.X) U.ι ≫ iN.hom.hom ∈
              ReductiveTorusCentralizer.centralizerPoints (𝟙 G) A) := by
  sorry

end AlgebraicGeometry
