module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Reductivity of smooth connected subdirect products

Source: Milne, Algebraic Groups (2017), Assertion 23.20 and its proof, printed p.491.
(blueprint: lem-sfb-subdirect-product-reductivity)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-- A smooth connected closed subgroup of a product of two reductive groups is
reductive when both coordinate projections are surjective on underlying spaces.
No condition is imposed on either projection kernel.

Source: Milne, Algebraic Groups (2017), Assertion 23.20, printed p.491.
(blueprint: lem-sfb-subdirect-product-reductivity)

Proof plan:
1. The reductive factors are smooth, hence reduced by
   sbc-lem-smooth-geometrically-reduced, applied to their structure morphisms.
   Thus their coordinate rings have no nonzero nilpotents (def-pc-reduced-scheme).
2. Factor each projection through its faithfully flat image using
   lem-sfb-affine-homomorphism-flat-image. The closed image is Spec(A/J) inside
   Spec(A). Topological surjectivity puts J in every prime. By
   lem-weil-pbc-zero-locus-eq-iff-radical-eq and reducedness, J is zero, so the
   closed image is the entire target and each projection is faithfully flat.
   This uses no smoothness of either kernel.
3. For any smooth connected normal unipotent closed subgroup N of H, factor
   each restricted projection N -> G_i through its faithfully flat image I_i
   using lem-sfb-affine-homomorphism-flat-image. Apply
   lem-sfb-unipotent-normal-quotient-image: I_i is smooth, connected, unipotent
   and normal in G_i, since H -> G_i is faithfully flat. All groups are affine
   of finite type, as required by these image results.
4. Reductivity makes both I_i trivial. For every F-algebra R, including
   nonreduced R, N(R) therefore maps to (1,1) in G_1(R) times G_0(R).
   The two closed subgroup inclusions are injective on R-points by
   def-sc-group-scheme-subgroup, so every point of N(R) is its identity.
5. Put C = F[N]. By def-weil-affine-spectrum, the universal point gives
   id_C = eta composed with epsilon. Also epsilon composed with eta = id_F,
   so N is the trivial group scheme. This applies to every such N and gives
   reductivity together with H's assumed smoothness and connectedness.
   The recorded reductivity predicate tests after algebraic closure; because F
   is algebraically closed, scalar extension to AlgebraicClosure F is an
   equivalence, preserving these subgroup and geometric-unipotence properties. -/
theorem isReductive_of_smooth_connected_subdirect_product
    {F : Type u} [Field F] [IsAlgClosed F]
    (G₁ G₀ H : Grp (Over (Spec (.of F))))
    (hG₁ : ReductiveTorusCentralizer.IsReductive G₁)
    (hG₀ : ReductiveTorusCentralizer.IsReductive G₀)
    [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (i : H ⟶ G₁ ⊗ G₀)
    [@IsClosedSubgroupScheme F _ H.X (G₁ ⊗ G₀).X H.grp (G₁ ⊗ G₀).grp i.hom.hom]
    [Surjective (i ≫ fst G₁ G₀).hom.hom.left]
    [Surjective (i ≫ snd G₁ G₀).hom.hom.left] :
    ReductiveTorusCentralizer.IsReductive H := by
  sorry

end AlgebraicGeometry
