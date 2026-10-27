module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.AlgebraicGeometry.ClosedImmersionProducts
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.SmoothAmbientNormalityGeometric
import Sheaf.AlgebraicGeometry.GroupScheme.ConnectedNormalSubgroupReductive
import Sheaf.AlgebraicGeometry.StandardGroupSchemes
import Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer
import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates
import WeilConjectures.AlgebraicGeometry.Dimension
import Sheaf.AlgebraicGeometry.DimZeroFiniteOverField

/-! # Normal subgroups meeting a maximal torus finitely

Source: Milne, Algebraic Groups (2017), Corollaries 17.85 and 21.53, pp.379--380
and 441, and the reduced-kernel argument in 23.24, p.492.
(blueprint: lem-sfb-reductive-normal-subgroup-torus-finiteness)

Finiteness is finiteness of the structure morphism over the field, equivalently
finite dimensionality of the coordinate algebra. The intersection is the pullback
in the category of schemes over the field. It retains all nilpotents.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A closed normal subgroup of a reductive group is finite if its scheme-theoretic
intersection with a split maximal torus is finite. The subgroup need not be smooth,
connected, or reduced.

Source: Milne, Corollaries 17.85 and 21.53, pp.379--380 and 441; 23.24, p.492;
Proposition 17.61(a), p.372; Propositions 11.1--11.2, pp.209--210.
(blueprint: lem-sfb-reductive-normal-subgroup-torus-finiteness)

Proof plan:
1. Put C = N° and M = C_red. By lem-sfb-locally-algebraic-group-identity-component,
   C is clopen and M is smooth connected finite type with the same underlying space.
   The reduction inclusion is closed by def-weil-pbc-scheme-reduction. Composing
   closed immersions using lem-weil-pbc-closed-immersion-products and applying
   lem-weil-pbc-closed-immersion-affine-cover-criterion makes N, C, and M affine.
2. Normality of N makes conjugation by each h in H(F) preserve C and its nilradical,
   hence M as a scheme. Apply lem-sfb-smooth-ambient-normality-geometric with smooth
   ambient group H and algebraic closure F itself to make M normal in H.
3. By lem-sfb-connected-normal-subgroup-reductive, M is reductive. Apply
   lem-sfb-normal-subgroup-maximal-torus-intersection to get the split maximal torus
   R = ((M ×_H S)_red)° in M, with its closed inclusion into M ×_H S.
4. By lem-weil-pbc-closed-immersion-base-change and
   lem-weil-pbc-closed-immersion-products, R embeds closed into N ×_H S. The affine
   criterion identifies F[R] as a quotient of the finite-dimensional algebra F[N ×_H S].
   By def-sc-gm-ga, a positive-rank split torus has infinitely many independent
   Laurent monomials. Therefore R has rank zero and is the trivial group.
5. Apply lem-sfb-reductive-torus-self-centralizer to M with maximal torus R = 1.
   The centralizer of 1 is all of M on every test algebra, so M = 1 as a scheme.
6. C has the same underlying space as M. By lem-sfb-group-neutral-component-translates,
   N has finitely many components, each a translate of C. Thus its underlying space
   is finite discrete and has dimension zero. Use lem-pc-scheme-dimension-local-rings
   and lem-pc-algebraic-dim-zero-affine-finite to conclude N is finite, retaining its
   nilpotents. By def-weil-finite-integral-morphism this is precisely finite-dimensional
   coordinates over F. -/
theorem reductive_normal_subgroup_finite_of_torus_intersection_finite
    {F : Type u} [Field F] [IsAlgClosed F]
    (H S N : Grp (Over (Spec (.of F))))
    (hH : ReductiveTorusCentralizer.IsReductive H)
    (iS : S ⟶ H) (hS : ReductiveTorusCentralizer.IsMaximalTorus iS)
    (hSplit : ∃ r : ℕ, Nonempty (S ≅ MultiplicativeType.splitTorus F r))
    (iN : N ⟶ H) [IsClosedSubgroupScheme iN.hom.hom]
    [IsNormalSubgroupScheme iN.hom.hom]
    (hFinite : IsFinite (pullback iN.hom.hom iS.hom.hom).hom) :
    IsFinite N.X.hom := by
  sorry

end AlgebraicGeometry
