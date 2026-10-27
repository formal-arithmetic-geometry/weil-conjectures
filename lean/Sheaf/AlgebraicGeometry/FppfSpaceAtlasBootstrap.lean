/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange
import WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE
import Sheaf.AlgebraicGeometry.EtaleRelationQuotient
import Sheaf.AlgebraicGeometry.EtaleRelationFindingOpens
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoproduct
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenGluing

/-! # Algebraicity from an fppf algebraic-space atlas

Source: Stacks Project, bootstrap.tex, Tag 04S6, theorem-final-bootstrap, condition (3)
(blueprint: lem-sfb-fppf-space-atlas-bootstrap).

The atlas is tested after every scheme-valued section. The resulting algebraic-space
projection is flat and locally finitely presented on étale scheme charts and surjective
on field-valued point classes. No condition on the diagonal of the target is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- An fppf sheaf admitting a surjective flat locally finitely presented algebraic-space
atlas is an algebraic space. `IsPullback` retains both projections and the canonical
scheme-test map; singleton `IsJointlySurjective` is surjectivity on point classes.
For a scheme target, testing every étale source chart is precisely testing compatible
étale source-and-target charts, by étale base change and locality of the scheme properties.
Source: Stacks Project, bootstrap.tex, Tag 04S6, theorem-final-bootstrap, condition (3)
(blueprint: lem-sfb-fppf-space-atlas-bootstrap).

Proof:
1. Choose a representable surjective étale scheme atlas A → U. Its composite p:A → F
   has algebraic-space scheme tests B_a = h_T ×_F h_A = P_a ×_U h_A, by
   lem-trf-space-fibre-products-etale-covers. Choose an étale scheme atlas W → B_a;
   its composite to P_a is representable surjective étale by
   lem-trf-space-representable-etale-scheme-tests. The assumed chart tests on P_a → T
   make W → T flat and locally finitely presented. The chart criterion
   lem-sfb-space-local-properties-chart-test gives those properties for B_a → T.
   Point classes lift successively through P_a and B_a, giving surjectivity.
2. Apply this at the section p of F(A). The kernel R = h_A ×_F h_A is an algebraic
   space with both projections flat locally finitely presented, by swapping factors.
   Its points on any test scheme are pairs with equal p-images. Thus R → h_(A×_S A)
   is a monomorphism and an equivalence relation: use diagonal pairs, swap, and
   composition (x,y),(y,z) ↦ (x,z). No diagonal hypothesis on F enters.
3. This monomorphism is chartwise locally of finite type. Locally its affine rings
   factor K → B_b → L with L finite type over K. The same generators, together with
   the image of b⁻¹, generate L over B. This is def-weil-finite-type-morphism.
   Apply lem-sfb-space-lft-monomorphism-separated-lqf and then
   lem-a1-separated-locally-qf-space-representable over A×_S A. Thus R is a scheme;
   the identity charts make its projections flat locally finitely presented.
4. The composite W → B_a → T of a surjective étale atlas with the test projection
   is surjective flat locally finitely presented, hence an fppf cover. Its universal
   pair lifts a to A. Thus p is locally surjective as a map of fppf sheaves.
5. The sectionwise quotient A(T)/R(T) injects into F(T). Local lifts from step 4
   glue their images under any map to an fppf sheaf G. Equality on overlaps follows
   from the kernel relation. Common refinements give independence and naturality.
   This is the sheafification universal property, def-weil-pbc-sheafification, so
   Q = A/R is canonically isomorphic to F.
6. Apply lem-sfb-fppf-space-relation-slicing to obtain V/D ≅ Q with flat locally
   finitely presented locally quasi-finite relation projections. Restrict to affine
   opens V_α. Flatness, local finite presentation, and local quasi-finiteness persist
   by base change, composition, and open restriction, using
   lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-qcqs-morphism-permanence,
   lem-pc-flat-compose, lem-sbc-locally-finite-presentation-composition,
   lem-weil-pbc-etale-composition-cancellation, def-weil-etale-morphism,
   lem-weil-pbc-separated-lqf-base-change, and lem-weil-pbc-lqf-restriction-to-opens.
7. On each affine V_α, lem-sfb-fppf-relation-etale-replacement gives a finite étale
   cover with quotients isomorphic to étale-relation quotients. They are algebraic
   spaces by lem-trf-etale-relation-quotient and map by representable open immersions
   to V_α/D_α by lem-trf-etale-relation-finding-opens.
8. Sections of V_α/D_α locally lift to V_α by
   lem-weil-pbc-site-sheafification-sections-local. Pull back the finite étale cover,
   using lem-weil-pbc-etale-covering-base-change; it is an fppf cover. Thus the open
   quotient pieces cover. Their finite coproduct is algebraic by
   lem-trf-algebraic-space-coproduct, with scheme atlases supplied by
   lem-weil-pbc-scheme-coproduct-family. Apply lem-trf-algebraic-space-open-gluing.
9. The V_α/D_α likewise cover V/D by representable opens, using local quotient lifts
   and the affine open cover of V. Choose its index bounded by the size of V.
   The atlas coproduct stays in the size convention, def-weil-size-convention.
   Apply the same coproduct and open-gluing results, then transport algebraicity
   along V/D ≅ Q ≅ F. Empty schemes and empty covers are included throughout. -/
theorem fppf_space_atlas_bootstrap {S : Scheme.{u}}
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (U : AlgebraicSpace S) (q : U.obj ⟶ F)
    (hatlas : ∀ (T : Over S) (a : F.obj.obj (op T)),
      ∃ (P : AlgebraicSpace S) (p : P.obj.obj ⟶ yoneda.obj T)
        (r : P.obj.obj ⟶ U.obj.obj),
        IsPullback r p q.hom (yonedaEquiv.symm a) ∧
        (∀ (V : Over S) (c : yoneda.obj V ⟶ P.obj.obj),
          IsEtale c → Flat (yoneda.preimage (c ≫ p)).left ∧
            LocallyOfFinitePresentation (yoneda.preimage (c ≫ p)).left) ∧
        IsJointlySurjective (fun _ : Unit ↦ p)) :
    IsAlgebraicSpace F := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
