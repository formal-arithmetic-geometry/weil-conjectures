module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.FieldPointFactorsThroughClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Realization of a closed subgroup of rational points

Source: Milne, Algebraic Groups (2017), Section 1(c), Theorem 1.45, printed p.19;
Stacks Project, Tag 01J3 (blueprint: lem-sfb-closed-rational-subgroup-realization).
The closed subscheme is the reduced induced structure on the closure of the given points.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The vanishing ideal of the closure of the underlying points of a rational subgroup.
Source: Milne, Theorem 1.45, printed p.19; Stacks, Tag 01J3
(blueprint: lem-sfb-closed-rational-subgroup-realization). -/
noncomputable def rationalSubgroupClosureIdeal {k : Type u} [Field k]
    (G : Over (Spec (.of k))) [GrpObj G]
    (S : Subgroup (𝟙_ (Over (Spec (.of k))) ⟶ G)) : G.left.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (X := G.left)
    (TopologicalSpace.Closeds.closure
      ((fun s : 𝟙_ (Over (Spec (.of k))) ⟶ G ↦
        s.left (IsLocalRing.closedPoint k)) '' (S : Set _)))

/-- The reduced induced closed subscheme on the Zariski closure of a rational subgroup,
with its structure morphism to the base field.
Source: Milne, Theorem 1.45, printed p.19; Stacks, Tag 01J3
(blueprint: lem-sfb-closed-rational-subgroup-realization). -/
noncomputable def rationalSubgroupClosure {k : Type u} [Field k]
    (G : Over (Spec (.of k))) [GrpObj G]
    (S : Subgroup (𝟙_ (Over (Spec (.of k))) ⟶ G)) : Over (Spec (.of k)) :=
  Over.mk ((rationalSubgroupClosureIdeal G S).subschemeι ≫ G.hom)

/-- The canonical inclusion of the reduced closure of a rational subgroup.
Source: Milne, Theorem 1.45, printed p.19; Stacks, Tag 01J3
(blueprint: lem-sfb-closed-rational-subgroup-realization). -/
noncomputable def rationalSubgroupClosureι {k : Type u} [Field k]
    (G : Over (Spec (.of k))) [GrpObj G]
    (S : Subgroup (𝟙_ (Over (Spec (.of k))) ⟶ G)) : rationalSubgroupClosure G S ⟶ G :=
  Over.homMk (U := rationalSubgroupClosure G S) (V := G)
    (rationalSubgroupClosureIdeal G S).subschemeι rfl

/-- A closed subgroup of rational points is realized by its reduced closure.
Source: Milne, Theorem 1.45 and proof, printed p.19
(blueprint: lem-sfb-closed-rational-subgroup-realization).

Proof:
1. The reduced-induced theorem gives a reduced closed immersion with image the closure T.
   Field-point factorization (lem-weil-pbc-field-point-factors-through-closed-immersion)
   identifies its rational points with T intersect G(k). The subspace closure identity
   and closedness of S identify this intersection with S; its lifts are dense in H.
2. H is finite type, being a closed subscheme of G. Apply
   lem-sfb-dense-rational-product-reduced to H and the dense lifted S: H times H is
   reduced and paired S-points are dense in its scheme topology.
3. The inverse images of T under multiplication and inversion are closed and contain
   the respective dense rational subsets, since S is a subgroup. Thus both maps have
   image in T. The unit lies in T since S contains the identity.
4. Apply lem-weil-pbc-reduced-source-factors-through-closed-subscheme to these maps,
   with reduced sources H times H, H and Spec k. Their unique factorizations through H
   are over k, since their composites with the inclusion are over k.
5. Compose the group diagrams with the closed immersion. They become the diagrams of G;
   cancel the immersion to obtain the group laws on H. The same monomorphism gives
   injectivity on R-points for every k-algebra R, hence a closed subgroup scheme.
   Step 1 gives the asserted equality of rational points. -/
theorem closed_rational_subgroup_realization {k : Type u} [Field k]
    (G : Over (Spec (.of k))) [GrpObj G]
    [IsSeparated G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (S : Subgroup (𝟙_ (Over (Spec (.of k))) ⟶ G))
    (hS : @IsClosed _
      (TopologicalSpace.induced
        (fun s : 𝟙_ (Over (Spec (.of k))) ⟶ G ↦ s.left (IsLocalRing.closedPoint k)) inferInstance)
      (S : Set _)) :
    ∃ hH : GrpObj (rationalSubgroupClosure G S),
      @IsClosedSubgroupScheme k _ (rationalSubgroupClosure G S) G hH _
        (rationalSubgroupClosureι G S) ∧
      Set.range (fun s : 𝟙_ (Over (Spec (.of k))) ⟶ rationalSubgroupClosure G S ↦
        s ≫ rationalSubgroupClosureι G S) = (S : Set _) := by
  sorry

end AlgebraicGeometry
