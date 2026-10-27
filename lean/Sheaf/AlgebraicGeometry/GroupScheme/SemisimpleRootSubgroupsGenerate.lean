module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality
import Sheaf.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus

/-! # Root subgroups generate a semisimple group

Source: Milne, Algebraic Groups (2017), Proposition 21.49(a), printed p.439,
with Theorem 21.11(c), printed pp.428--430.
(blueprint: lem-sfb-semisimple-root-subgroups-generate)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.TorusCharacterTangent

/-- A closed subgroup containing every root subgroup of a split semisimple group is
all of the group. The family is indexed by nontrivial characters with nonzero actual
character weight space. Its members are exactly the unique root subgroups described
by reductive_root_subgroup_parametrizations. Equality of closed subgroup schemes is
expressed by the inclusion being an isomorphism; K need not be smooth or connected.

Source: Milne, Proposition 21.49(a), printed p.439, and Theorem 21.11(c), pp.428--430.
(blueprint: lem-sfb-semisimple-root-subgroups-generate)

Proof:
1. Use lem-sfb-reductive-rank-one-reflections for the character/cocharacter lattices,
   their perfect pairing and the canonical coroots. By lem-sfb-semisimple-roots-span,
   the coroots span the rational cocharacter space.
2. For each root use lem-sfb-opposite-root-sl2-parametrizations. Over every F-algebra,
   multiply x₊(s)x₋(-s⁻¹)x₊(s) to obtain w(s), and w(s)w(1)⁻¹ = diag(s,s⁻¹).
   Both root inclusions factor through K, so these products define a factorization
   of the coroot through K, including over nonreduced test algebras.
3. The intersection D = T ×_G K is diagonalizable by
   lem-sfb-split-torus-subgroups-diagonalizable. By
   lem-sfb-multiplicative-character-antiduality, X*(T) → X*(D) is surjective.
   Every element of its kernel pairs to zero with every coroot. Rational spanning,
   perfectness and torsion freeness make this kernel zero. Antiduality then makes
   D → T an isomorphism, so T factors through K. No primitivity assertion is used.
4. The root decomposition in lem-sfb-reductive-rank-one-reflections and the tangent
   description in lem-sfb-reductive-root-subgroup-parametrizations show that the
   tangent images of T and all root groups span Lie(G). The torus is smooth and
   connected by lem-sfb-multiplicative-type-largest-subtorus. Apply
   lem-sfb-smooth-subgroup-tangent-generation to this finite family to obtain K = G.
5. If the root family is empty, rational coroot spanning forces T to have rank zero.
   Step 3 still applies, and step 4 applies to the singleton family containing T.
   Thus the empty-root case is included without a nonemptiness assumption. -/
theorem semisimple_rootSubgroups_generate
    (F : Type u) [Field F] [IsAlgClosed F]
    (G T : Grp (Over (Spec (.of F))))
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (hsemisimple : IsSemisimpleGroupScheme G.X)
    (i : T ⟶ G) (hT : ReductiveTorusCentralizer.IsMaximalTorus i)
    (r : ℕ) (hsplit : Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    [ModObj T.X G.X]
    (hconj : γ[T.X,G.X] =
      (fst T.X G.X ≫ i.hom.hom) * snd T.X G.X * (fst T.X G.X ≫ i.hom.hom)⁻¹)
    (U : {α : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F) //
      α.hom.hom ≠ 1 ∧ weightSpace T G α ≠ ⊥} → Grp (Over (Spec (.of F))))
    (j : ∀ α, U α ⟶ G)
    (hU : ∀ α, IsClosedSubgroupScheme (j α).hom.hom ∧
      Smooth (U α).X.hom ∧ ConnectedSpace (U α).X.left ∧ IsStable T G (j α) ∧
      (GrpObj.differential (j α).hom.hom).toLinearMap.range = weightSpace T G α.val)
    (K : Grp (Over (Spec (.of F)))) (k : K ⟶ G)
    (hK : IsClosedSubgroupScheme k.hom.hom)
    (hcontains : ∀ α, ∃ f : U α ⟶ K, f ≫ k = j α) : IsIso k := by
  sorry

end AlgebraicGeometry.TorusCharacterTangent
