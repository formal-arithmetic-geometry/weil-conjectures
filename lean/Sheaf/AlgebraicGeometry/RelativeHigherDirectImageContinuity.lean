/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos
import Sheaf.AlgebraicGeometry.AffineEtaleSiteColimitStatement
import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
import Sheaf.CategoryTheory.CohomologyColimitSites
import WeilConjectures.CategoryTheory.ColimitSites
import WeilConjectures.CategoryTheory.FilteredColimitCategories
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs

/-!
# Relative higher-direct-image continuity with varying base

Source: Stacks Project, Tag 0EYM, lemma-relative-colimit-general, statement and the
first two proof paragraphs (blueprint: lem-kun-0eym).

The comparison is induced by the commutative-square derived mate, followed by the
coefficient maps. The diagrams and cocones are presented with explicit object
isomorphisms and equations prescribing every transition and leg.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Degree-q commutative-square exchange followed by the coefficient map.

Source: Stacks Project, Tag 0EYM, first proof paragraph; Tag 07A7, remark-base-change
(blueprint: lem-kun-0eym).
The first factor identifies inverse image of cohomology with cohomology of inverse
image. The second takes cohomology of the derived mate `derivedBaseChangeMapPlus` and
of the specified coefficient map, using the exact pullback comparison with degree zero.
No cartesian or torsion hypothesis enters this construction. -/
noncomputable def relativeHigherDirectImageExchange
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} g').obj F ⟶ F') (q : ℕ) :
    (upperStar AddCommGrpCat.{u + 1} g).obj
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) ⟶
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F')) :=
  ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlusHomologyFunctorIso
    (q : ℤ)).hom.app
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) ≫
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F) ≫
        (rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').map
          (((upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlusSingleFunctor
            0).hom.app F ≫
            (DerivedCategory.Plus.singleFunctor
              (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).map φ))

/-- Relative higher direct images commute with the specified filtered coefficient
colimit along an inverse system with affine transitions on both sources and bases.

Source: Stacks Project, Tag 0EYM, lemma-relative-colimit-general
(blueprint: lem-kun-0eym).
`η` and `hu` express the compatible stage arrows and their limit. `hφid` and
`hφcomp` are the coefficient-system laws. `eA` and `hA` present the inverse-image
coefficient diagram, and `hcA` identifies its colimit. `eH` and `hH` prescribe the
pulled-back higher-image diagram; `hlegs` prescribes its canonical comparison legs.
The conclusion says exactly that the comparison obtained by colimit descent is an
isomorphism. All coefficients are arbitrary abelian sheaves and all squares merely commute.

Proof:
1. Use the commutative-square exchange of [def-kun-commutative-derived-exchange], whose
   inverse-image square isomorphism is constructed from composition and the commutativity
   equality, with no cartesian hypothesis. Write $G_i=R^qu_{i,*}A_i$ and let
   $\psi_{ji}:b_{ji}^{-1}G_i\to G_j$ be exchange followed by $R^qu_{j,*}(\phi_{ji})$, as
   specified in the statement. These maps satisfy the system and cone laws. Indeed the square
   isomorphism for $k\to i$ is the pasted square isomorphism for $k\to j\to i$: both are the
   composition comparison between inverse images along the equal maps $u_i a_{ki}=b_{ki}u_k$, by
   associativity of the inverse-image composition isomorphisms. Apply part (1) of mate pasting
   to these isomorphisms and part (4) to the identity square. Naturality in the coefficient,
   followed by $\phi_{ki}=\phi_{kj}\circ a_{kj}^{-1}\phi_{ji}$, gives $\psi_{ki}=\psi_{kj}\circ
   b_{kj}^{-1}\psi_{ji}$, with the composition identifications understood. For the cone law
   write $c_i:a_i^{-1}A_i\to A$ for the coprojections, $E_i:b_i^{-1}G_i\to R^qu_*a_i^{-1}A_i$
   for projection exchange, and $\lambda_i=R^qu_*(c_i)\circ E_i$. Pasting the transition square
   $j\to i$ with the projection square at $j$ gives projection exchange at $i$. Naturality of
   its mate in $A_i$ therefore rewrites $\lambda_j\circ b_j^{-1}\psi_{ji}$ as $R^qu_*(c_j\circ
   a_j^{-1}\phi_{ji})\circ E_i$. The colimit cocone relation $c_j\circ a_j^{-1}\phi_{ji}=c_i$
   makes this $\lambda_i$, under the inverse-image composition identifications. Taking
   degree-$q$ cohomology respects these equalities because inverse image is exact. Thus
   $L=\varinjlim_i b_i^{-1}G_i$ and the specified map $C_u:L\to R^qu_*A$ are defined. This is an
   application of abstract mates to commutative squares, so no cartesian-square exchange-pasting
   statement is being used.
   Uses: def-kun-commutative-derived-exchange, lem-weil-pbc-mate-pasting,
   lem-weil-pbc-derived-inverse-image-composition,
   prop-weil-pbc-derived-inverse-image-adjunction, prop-weil-pbc-inverse-image-exact,
   def-weil-pbc-adjunction-mate, lem-weil-pbc-exact-functor-complex-cohomology.
2. It suffices to prove the comparison after replacing the bases by affine opens pulled back
   from one stage. Fix $i_0$. The tail $j\ge i_0$ is cofinal: any finite collection of indices
   has an upper bound together with $i_0$. Hence restricting all colimits and inverse limits to
   this tail does not change them (a compatible cone or cocone extends uniquely by choosing an
   upper bound, and two choices agree at a further upper bound). Cover $B_{i_0}$ by affine opens
   $W_{i_0}$ and put $W_j=b_{ji_0}^{-1}W_{i_0}$ and $Z_j=u_j^{-1}W_j$. Then $W_j$ is affine,
   $Z_j\to W_j$ is qcqs, and $Z_k=a_{kj}^{-1}Z_j$ for $k\ge j$. The restricted transitions are
   affine by base change. The restricted limits are $W=b_{i_0}^{-1}W_{i_0}$ and $Z=u^{-1}W$, by
   the open-restriction assertion for affine-transition limits; the equalities
   $Z_j=a_{ji_0}^{-1}Z_{i_0}$ justify its use on the sources as well. All $Z_j$ are qcqs by
   permanence. Etale inverse image along an open immersion is restriction and preserves
   colimits, so $A|_Z=\varinjlim_j(A_j|_{Z_j})|_Z$, and $L|_W$ is the corresponding restricted
   colimit. Higher direct image restricts to the higher direct image of the restricted morphism:
   on every etale object over $W_j$ (or $W$), the cohomology presheaf of the restricted morphism
   is the original presheaf evaluated on that object; local representation and local equality
   for sheafification give the same associated sheaf. To check the restricted maps, take an
   etale test object over $W_j$ and its base change at a later stage or at the limit. The chart
   lemma expresses the original exchange and the exchange for the restricted morphisms, after
   precomposition by the chart map, as pullback along the same map between the fibre products
   with that test object. Coefficient naturality then gives the same formula for the transitions
   and legs. Every section is locally in the image of a chart map by the cited
   sheafification-local-representation statement; hence equality after those chart maps implies
   equality of the sheaf morphisms. Therefore the restricted comparison is exactly the same
   construction for $Z_j\to W_j$. Prove this on each $W$; these opens cover $B$. Rename the
   restricted systems $V_j\to B_j$. We may now assume the $B_j$ affine and the $V_j$ qcqs.
   Uses: lem-weil-pbc-limit-affine-transition, lem-weil-pbc-affine-morphism-permanence,
   lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-etale-inverse-image-restriction,
   lem-weil-pbc-left-adjoint-preserves-colimits, sbc-lem-higher-direct-image-presheaf,
   lem-weil-pbc-site-sheafification-sections-local, lem-kun-commutative-exchange-chart.
3. Use the equivalence between abelian sheaves on the small etale site and the finite-cover
   affine etale site. By the affine-etale colimit theorem, every affine etale $U\to B$ has a
   model $U_i\to B_i$, and all its base changes $U_j=U_i\times_{B_i}B_j$ for $j\ge i$ are
   affine. The theorem also supplies strictification, descent of morphisms and descent of finite
   standard covers. Apply cohomology of colimit sites in degree zero to the system $G_j$ with
   transitions $\psi_{kj}$. Since $H^0(U_j,G_j)=G_j(U_j)$, this gives, canonically and with the
   specified transition maps, $$L(U)=\varinjlim_{j\ge i}G_j(U_j).$$ Here the restriction
   equivalences identify the inverse images and their units: their right adjoints on each affine
   test object are the same evaluation on its base change, so uniqueness of the left adjoint
   gives the unit-compatible identifications. Site equivalences preserve the colimit by its
   universal property. The degree-zero specialization is used only for sections of $G_j$, not
   for the higher direct images themselves.
   Uses: lem-weil-pbc-affine-etale-site-topos, lem-weil-pbc-affine-etale-site-colimit,
   lem-weil-pbc-cohomology-colimit-of-sites, def-weil-pbc-sites-and-cohomology.
4. For this model set $T_j=V_j\times_{B_j}U_j$ and $T=V\times_BU$. Each $T_j$ is qcqs: $T_j\to
   U_j$ is a base change of the qcqs $u_j$, and $U_j$ is affine. For $k\ge j$, $T_k\cong
   V_k\times_{V_j}T_j$, because $U_k=U_j\times_{B_j}B_k$ and the original square commutes. Thus
   $T_k\to T_j$ is affine, even though $V_k\to V_j$ need not be a base change of $B_k\to B_j$.
   The projections exhibit $T=\varprojlim_{j\ge i}T_j$: maps to the $T_j$ amount to compatible
   maps to the $V_j$ and $U_j$ with equal images in the $B_j$, hence to maps to $V$ and $U$ with
   equal images in $B$. Restrict $A_j$ to $T_j$ and call it $A_{j,T_j}$. The induced coefficient
   system has limit coefficient $A|_T$, since inverse images compose and commute with colimits.
   The cohomology-continuity theorem for varying abelian sheaves consequently gives the
   canonical isomorphism $$\alpha_U:\varinjlim_{j\ge
   i}H^q(T_j,A_{j,T_j})\xrightarrow{\sim}H^q(T,A|_T).$$ The maps are exactly pullback on
   cohomology followed by the coefficient transitions. This argument applies after any
   replacement of $U_i$ by an affine etale object at any later stage.
   Uses: lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-affine-morphism-permanence,
   def-pc-fibre-product, lem-weil-pbc-left-adjoint-preserves-colimits,
   lem-weil-pbc-derived-inverse-image-composition,
   lem-weil-pbc-etale-cohomology-limit-of-schemes.
5. Put $P_j(U_j)=H^q(T_j,A_{j,T_j})$ and $P(U)=H^q(T,A|_T)$, with canonical sheafification maps
   $\theta_j:P_j(U_j)\to G_j(U_j)$ and $\theta:P(U)\to(R^qu_*A)(U)$. The commutative-square
   chart compatibility lemma, first for a transition square and then for a projection square,
   followed by naturality for the coefficient maps, gives $$C_u(U)\circ
   h_U=\theta\circ\alpha_U,$$ where $h_U:\varinjlim_{j\ge i}P_j(U_j)\to L(U)$ is induced by the
   $\theta_j$ and the section formula of step 3. In particular, this is a commutative diagram
   with top row $\varinjlim P_j\to L(U)$, bottom row $P(U)\to R^qu_*A(U)$, left vertical arrow
   $\alpha_U$ an isomorphism, and right vertical arrow the specified $C_u(U)$. It is a diagram
   for the actual mate-defined comparison, not just for some isomorphism between the objects.
   Uses: lem-kun-commutative-exchange-chart, sbc-lem-higher-direct-image-presheaf.
6. Let $s\in(R^qu_*A)(U)$. Locally on $U$, the sheafification description and local
   representation provide $z\in P(U)$ mapping to $s$; refine the cover by affine etale objects.
   Each such object has a model at some stage by affine-etale descent, and step 4 gives
   $z=\alpha_U(\zeta)$ for a class $\zeta\in\varinjlim_jP_j(U_j)$. Then step 5 gives
   $C_u(h_U(\zeta))=s$. Thus $C_u$ is locally surjective on the affine etale site.
   Uses: sbc-lem-higher-direct-image-presheaf, lem-weil-pbc-site-sheafification-sections-local,
   lem-weil-pbc-affine-etale-site-topos, lem-weil-pbc-affine-etale-site-colimit.
7. Let $\xi\in L(U)$ have $C_u(\xi)=0$. By the section formula of step 3 and the elementwise
   description of a filtered colimit of abelian groups (integer modules), choose a stage $j\ge
   i$ and $\xi_j\in G_j(U_j)$ representing $\xi$. Since $G_j$ is the sheafification of $P_j$,
   there is a finite standard affine etale cover $\{U_{j,k}\to U_j\}$ on which $\xi_j$ lifts to
   $z_{j,k}\in H^q(V_j\times_{B_j}U_{j,k},A_j)$. Pull this cover back to $U$ and work on one
   member. Step 5 says the image of the pulled-back raw class in $R^qu_*A$ is zero. The
   local-equality property of sheafification, applied to that raw class and zero, gives a
   further affine etale cover on which the raw limit class itself is zero. Descend each of these
   affine objects to some stage. Choose a common upper bound of that stage and $j$, then use
   morphism descent to represent its map to $U_{j,k}$ after enlarging this upper bound once
   more. The coefficient on the new chart is pulled back from $A_j$ and mapped into the later
   $A_l$ by the given coefficient transition; this is exactly the restriction of the original
   raw class in the system of step 4, by the coefficient and test-object naturality in step 5.
   Different covering members may use different later stages, since we seek local vanishing. On
   each resulting object step 4 applies, so injectivity of $\alpha$ says that the restricted raw
   class is zero in the colimit of the $P_l$. Its image under $h$ is therefore zero. That image
   is precisely the restriction of $\xi$, by the diagram of step 5 and the restriction maps of
   the stage sheafification maps. Hence $\xi$ is locally zero. This does not infer global
   vanishing of a cohomology class from vanishing of its sheafification; the second local
   refinement is essential.
   Uses: lem-weil-pbc-filtered-colimit-modules-elementwise,
   sbc-lem-higher-direct-image-presheaf, lem-weil-pbc-site-sheafification-sections-local,
   lem-weil-pbc-affine-etale-site-topos, lem-weil-pbc-affine-etale-site-colimit.
8. For any two local sections with equal images, apply step 7 to their difference. Thus $C_u$ is
   locally injective as well as locally surjective. Apply the locally-bijective criterion for
   sheafification to this morphism viewed as a map of presheaves of abelian groups; its source
   and target are already sheaves, so their sheafifications are themselves. It follows that
   $C_u$ is an isomorphism on the affine etale site, hence on the small etale site by the
   restriction equivalence. Finally the open cover in step 2 gives local injectivity and local
   surjectivity on the original base, and the same criterion gives the original isomorphism. All
   cohomology-continuity and sheafification results used here apply to arbitrary abelian
   sheaves, including nontorsion ones.
   Uses: lem-weil-pbc-site-sheafification-iso-locally-bijective,
   lem-weil-pbc-affine-etale-site-topos.
-/
theorem higherDirectImage_relative_continuity
    {I : Type u} [PartialOrder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (DV DB : Iᵒᵖ ⥤ Scheme.{u}) (η : DV ⟶ DB)
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DV.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DB.map a)]
    [∀ i : Iᵒᵖ, QuasiCompact (η.app i)]
    [∀ i : Iᵒᵖ, QuasiSeparated (η.app i)]
    (cV : Cone DV) (hcV : IsLimit cV) (cB : Cone DB) (hcB : IsLimit cB)
    (v : cV.pt ⟶ cB.pt)
    (hu : ∀ i : Iᵒᵖ, cV.π.app i ≫ η.app i = v ≫ cB.π.app i)
    (F : ∀ i : I, Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (a : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (DV.map a.op)).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (DV.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (DV.obj (op i))).hom.app (F i))
    (hφcomp : ∀ (i j k : I) (a : i ⟶ j) (b : j ⟶ k),
      φ (a ≫ b) =
        (upperStarComp AddCommGrpCat.{u + 1} (DV.map b.op) (DV.map a.op)
          (DV.map (a ≫ b).op) (DV.map_comp b.op a.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (DV.map b.op)).map (φ a) ≫ φ b)
    (A : I ⥤ Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eA : ∀ i : I, A.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op i))).obj (F i))
    (hA : ∀ (i j : I) (a : i ⟶ j), A.map a =
      (eA i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (cV.π.app (op j)) (DV.map a.op)
          (cV.π.app (op i)) (cV.w a.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op j))).map (φ a) ≫ (eA j).inv)
    (cA : Cocone A) (hcA : IsColimit cA) (q : ℕ)
    (H : I ⥤ Sheaf cB.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (cB.π.app (op i))).obj
        ((DerivedCategory.Plus.homologyFunctor
          (Sheaf (DB.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} (η.app (op i))).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
              (F i)))))
    (hH : ∀ (i j : I) (a : i ⟶ j), H.map a =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (cB.π.app (op j)) (DB.map a.op)
          (cB.π.app (op i)) (cB.w a.op).symm).hom.app
          ((DerivedCategory.Plus.homologyFunctor
            (Sheaf (DB.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
            ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} (η.app (op i))).obj
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
                (F i)))) ≫
        (upperStar AddCommGrpCat.{u + 1} (cB.π.app (op j))).map
          (relativeHigherDirectImageExchange ⟨η.naturality a.op⟩ (F i) (F j) (φ a) q) ≫
        (eH j).inv)
    (cH : Cocone H) (hcH : IsColimit cH)
    (legs : H ⟶ (Functor.const I).obj
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf cB.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} v).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj cA.pt))))
    (hlegs : ∀ i : I, legs.app i = (eH i).hom ≫
      relativeHigherDirectImageExchange ⟨hu (op i)⟩ (F i) cA.pt
        ((eA i).inv ≫ cA.ι.app i) q) :
    IsIso (hcH.desc
      { pt := (DerivedCategory.Plus.homologyFunctor
          (Sheaf cB.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} v).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj cA.pt))
        ι := legs }) := by
  sorry

end AlgebraicGeometry.Etale
