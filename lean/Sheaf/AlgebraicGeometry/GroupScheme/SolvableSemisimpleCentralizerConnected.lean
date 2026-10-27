module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Sheaf.AlgebraicGeometry.SemisimpleGroupSchemePoint
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothConnectedDerivedSubgroup
import Sheaf.AlgebraicGeometry.SmoothAmbientNormalityGeometric
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomRationalPoints

/-! # Connected centralizers of semisimple points in solvable groups

Source: Milne, Algebraic Groups (2017), Theorem 16.40, printed pp.338--339,
connectedness assertion (blueprint: lem-sfb-solvable-semisimple-centralizer-connected).

The centralizer is the scheme-theoretic equalizer of right and left multiplication
by the specified rational point, retaining its values on nonreduced test algebras.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonObj

namespace AlgebraicGeometry

/-- The scheme-theoretic centralizer of a semisimple point in a smooth connected
solvable affine algebraic group is connected.
Source: Milne, Algebraic Groups (2017), Theorem 16.40, printed pp.338--339
(blueprint: lem-sfb-solvable-semisimple-centralizer-connected).

Proof:
1. Induct on the least scheme-theoretic derived length. For a commutative group,
   including the trivial group of derived length zero, the equalizer is G itself.
2. By lem-sfb-smooth-connected-derived-subgroup, successive derived groups are smooth
   and connected. Minimality makes them invariant under conjugation, and
   lem-sfb-smooth-ambient-normality-geometric makes them normal. Let N be the last
   nontrivial derived group. It is commutative. By
   lem-sfb-lie-kolchin-triangular-embedding, G embeds in upper triangular matrices;
   commutators have diagonal 1, so N is unipotent.
3. By lem-sfb-affine-normal-quotient-geometry form Q = G/N, smooth and connected.
   Its derived series lies in the images of that of G, so its derived length is
   strictly smaller. The image of s is semisimple, since representations pull back.
   Induction gives connectedness of D = C_Q(s mod N).
4. By lem-sfb-semisimple-fixed-subscheme-smooth applied to conjugation on G, N and Q,
   the equalizers C = C_G(s), K = C_N(s) and D are smooth. By
   lem-sfb-semisimple-commutative-unipotent-commutator, K is connected and every
   element of N(k) is a product [s,u]v with u in N(k), v in K(k).
5. By lem-sfb-affine-group-homomorphism-image lift y in D(k) to z in G(k).
   Then [s,z] is in N(k), so write it as [s,u]v. Rearranging gives
   z s⁻¹ z⁻¹ = u s⁻¹ u⁻¹ v, with v commuting with the second factor.
6. In the faithful triangular representation, the second factor is semisimple and
   v is unipotent. By lem-sfb-multiplicative-jordan-linear-compatibility, uniqueness
   forces v = 1. Thus u⁻¹z centralizes s and lifts y: C(k) maps onto D(k).
7. The restriction C → D has scheme-theoretic kernel K on every algebra. By
   lem-sfb-affine-group-homomorphism-image and smoothness of D, it is faithfully flat.
8. Form C/K by lem-sfb-affine-normal-quotient-geometry. The quotient universal
   properties, using lem-sfb-faithfully-flat-group-quotient-universal, identify C/K
   with D. Apply the inverse-image connectedness clause of the quotient-geometry
   lemma to the whole subgroup C/K, with its smooth connected kernel K and smooth
   connected target D. Its inverse image C is connected, completing the induction. -/
theorem solvable_semisimple_centralizer_connected
    {k : Type u} [Field k] [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [Smooth G.hom] [ConnectedSpace G.left]
    (hsolv : IsSolvableGroupScheme G)
    (s : StandardGroupSchemes.affine k k ⟶ G)
    (hs : IsSemisimpleGroupSchemePoint G s) :
    ConnectedSpace
      (equalizer
        (𝟙 G * (Over.homMk G.hom (by
          simp only [StandardGroupSchemes.affine, algSpec_obj_hom,
            Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
          exact Category.comp_id G.hom) ≫ s))
        ((Over.homMk G.hom (by
          simp only [StandardGroupSchemes.affine, algSpec_obj_hom,
            Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
          exact Category.comp_id G.hom) ≫ s) * 𝟙 G)).left := by
  sorry

end AlgebraicGeometry
