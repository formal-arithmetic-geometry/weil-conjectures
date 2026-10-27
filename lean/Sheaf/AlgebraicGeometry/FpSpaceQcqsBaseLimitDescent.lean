/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.EtaleAtlasPresentation
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.DescendMonomorphism
import Sheaf.AlgebraicGeometry.EtaleRelationQuotient
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover

/-! # Finite-presentation algebraic-space descent over qcqs scheme limits

Source: Stacks Project, Limits of Spaces, Tag 07SK, lemma-descend-finite-presentation,
restricted to scheme bases
(blueprint: lem-sfb-fp-space-qcqs-base-limit-descent).

The bases are schemes over Spec Z, equivalently arbitrary schemes. Pullbacks below are
presheaf pullbacks of fppf sheaves and hence the sheaf fibre products. The over-category
records that every map and isomorphism respects the indicated base scheme. Neither a
stage base nor the limiting base is required to be affine.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Objects, morphisms, and equality of finitely presented algebraic spaces descend
along nonempty directed inverse systems of qcqs schemes with affine transitions.
Finite presentation is the conjunction of local finite presentation on every etale
scheme chart, affine-test quasi-compactness, and quasi-compactness of the relative diagonal.
The morphism comparison is Mathlib's canonical composition isomorphism, transported
along the cone equation and Yoneda functoriality.
Source: Stacks Project, Limits of Spaces, Tag 07SK, lemma-descend-finite-presentation,
scheme-base specialization (blueprint: lem-sfb-fp-space-qcqs-base-limit-descent).

Proof:
1. Fix an index $0$ and restrict to the cofinal directed tail $J_{\ge0}$. A cone on this tail
   extends uniquely to the original diagram: for $a\in J$ choose $b\ge a,0$ and compose its
   $b$-component with $T_b\to T_a$; a common upper bound shows independence. Thus its limit is
   still $T$. By [lem-weil-pbc-limit-affine-transition], $T\to T_0$ is affine. By
   [lem-weil-pbc-affine-morphism-permanence](3) it is quasi-compact and quasi-separated, so
   [lem-weil-pbc-qcqs-morphism-permanence](2) shows that $T$ is qcqs. Base change preserves
   finite presentation by [lem-sfb-space-flat-proper-fp-locality], so all finite-stage pullbacks
   below remain finitely presented.
2. Let $Y\to T$ be finitely presented. By [lem-sfb-space-fp-qcqs-source], $Y$ is qcqs. Choose an
   affine scheme atlas $q:W\to Y$ by [lem-sfb-qc-space-affine-etale-atlas]. The chart criterion
   [lem-sfb-space-local-properties-chart-test], with identity target chart $T\to T$, makes $W\to
   T$ locally finitely presented. The affine scheme $W$ is qcqs by
   [lem-weil-pbc-affine-scheme-qcqs]; scheme permanence
   [lem-weil-pbc-qcqs-morphism-permanence](1) makes $W\to T$ quasi-compact and quasi-separated,
   hence finitely presented. By [lem-a1-etale-atlas-presentation], $R=W\times_YW$ is a scheme,
   its projections $s,t$ are etale, $(s,t)$ is a monomorphism and an equivalence relation, and
   $Y$ is its sheaf quotient.
3. By [lem-sfb-qcqs-space-fibre-product], $R=W\times_YW$ is qcqs. Since $s:R\to W$ is etale, it
   is locally finitely presented by [def-weil-etale-morphism]. Composition
   [lem-sbc-locally-finite-presentation-composition] with $W\to T$ makes $R\to T$ locally
   finitely presented. Its source is qcqs and $T$ is quasi-separated, so
   [lem-weil-pbc-qcqs-morphism-permanence](1) gives the two other finiteness conditions. Thus
   both schemes $W,R$ are finitely presented over the possibly nonaffine scheme $T$. This
   supplies the finiteness check needed before scheme descent; $R$ need not be affine.
4. Apply clauses (1) and (2) of [thm-pd-spreading-out] to the schemes $W,R$ and the maps $s,t$.
   At a common stage $i$ this gives finitely presented schemes $W_i,R_i$ over $T_i$ and maps
   $s_i,t_i:R_i\rightrightarrows W_i$ with the given limiting presentation. Directedness
   supplies common stages, and [lem-weil-pbc-qcqs-morphism-permanence](3) preserves their finite
   presentation on enlargement. Its (2) makes every such $W_i,R_i$ qcqs. The hypotheses of the
   scheme theorem hold because every $T_i$ is qcqs and the transitions are affine. No affineness
   of $T_i$ is used.
5. We check the local finiteness hypotheses for property descent. A map between schemes finitely
   presented over $T_i$ is locally finitely presented. Indeed, near any source point choose an
   affine open $\operatorname{Spec}A\subset T_i$, an affine target open over it, and an affine
   source open mapping into that target. By [lem-weil-pbc-lfp-affine-opens-finite-presentation]
   their rings have finite presentations $C=A[y_1,\ldots,y_m]/J$ and $B=A[x_1,\ldots,x_n]/K$. If
   the given map sends $y_a$ to $p_a(x)$, then $B=C[x_1,\ldots,x_n]/(K(x),y_a-p_a(x))$. These
   are finitely many relations by [def-weil-pbc-finitely-presented-algebra], proving local
   finite presentation by [def-sbc-locally-finite-presentation], and local finite type by
   forgetting the relations. Scheme products of finitely presented objects over $T_i$ are
   finitely presented, using base change [lem-weil-pbc-qcqs-morphism-permanence](3) and
   composition [lem-weil-pbc-proper-fp-permanence](d). Thus this applies to $s_i,t_i$ and
   $j_i=(s_i,t_i):R_i\to W_i\times_{T_i}W_i$; their sources and targets are qcqs by permanence
   (2).
6. The limit maps $s,t$ are etale and $j=(s,t)$ is a monomorphism. Apply
   [lem-weil-pbc-descend-etale] to $s_i,t_i$ and [lem-weil-pbc-descend-monomorphism] to $j_i$ to
   make these properties hold at one later stage. All three applications have qcqs base, source
   and target; the necessary local finite presentation or local finite type was checked in step
   5. Etaleness persists on enlargement by [lem-weil-pbc-etale-scheme-base-change].
   Monomorphisms persist too: two maps into a pullback with equal composites into its target
   have equal composites into its original source, by monicity, and equal base components, hence
   are equal by the pullback universal property.
7. The relation axioms must also descend. At the limit the kernel pair has $e:W\to R$, $v:R\to
   R$ and $c:R\times_{t,W,s}R\to R$ given by $w\mapsto(w,w)$, $(w_1,w_2)\mapsto(w_2,w_1)$ and
   $((w_1,w_2),(w_2,w_3))\mapsto(w_1,w_3)$. By step 5, $s_i,t_i$ are locally finitely presented,
   and by [lem-weil-pbc-qcqs-morphism-permanence](1) they are quasi-compact and quasi-separated.
   Consequently $P_i=R_i\times_{t_i,W_i,s_i}R_i$ is finitely presented over $T_i$, by its (3)
   and [lem-weil-pbc-proper-fp-permanence](d). Clause (2) of [thm-pd-spreading-out] descends
   $e,v,c$ to a common later stage. Clause (3) makes the finitely many equations
   $s_ie_i=t_ie_i=\mathrm{id}$, $s_iv_i=t_i$, $t_iv_i=s_i$, $s_ic_i=s_i\operatorname{pr}_1$,
   $t_ic_i=t_i\operatorname{pr}_2$ hold there. On points of every test scheme these exhibit
   reflexivity, symmetry and transitivity. Together with monicity of $j_i$, they make
   $R_i\rightrightarrows W_i$ an etale equivalence relation.
8. By [lem-trf-etale-relation-quotient], the sheaf quotient $Y_i=W_i/R_i$ is an algebraic space,
   with a representable surjective etale atlas $W_i\to Y_i$ whose kernel pair is $R_i$. Since
   $W_i,R_i$ are qcqs, [lem-weil-pbc-qcqs-morphism-permanence](1) makes $R_i\to W_i$
   quasi-compact. Hence [lem-sfb-space-qs-atlas-criterion] makes $Y_i$ quasi-separated. It is
   quasi-compact: its atlas has quasi-compact source, as in the definition in the item;
   equivalently, continuity and surjectivity of the point map in
   [lem-a1-space-affine-etale-cover] pull an open cover back to $W_i$, where a finite subcover
   exists, and surjectivity makes the same finite family cover $Y_i$. The chart criterion
   [lem-sfb-space-local-properties-chart-test] applied to $W_i\to Y_i$ and the identity chart on
   $T_i$ gives local finite presentation of $Y_i\to T_i$. Finally
   [lem-sfb-space-qcqs-permanence] gives quasi-compactness and quasi-separatedness of this
   morphism because $Y_i$ is qcqs and $T_i$ is quasi-separated. Thus $Y_i\to T_i$ is finitely
   presented.
9. Base change of this atlas to $T$ is an etale surjective atlas with kernel pair $R$ by
   [lem-trf-space-fibre-products-etale-covers]. By [lem-a1-etale-atlas-presentation], both $Y$
   and $Y_i\times_{T_i}T$ are the sheaf quotient of the same relation $R\rightrightarrows W$.
   The universal property of [lem-trf-etale-relation-quotient] gives maps in both directions
   induced by the identity on $W$. Each composite restricts to the identity on $W$, so quotient
   uniqueness makes it the identity. The maps respect $T$, since their composites to $T$ agree
   on $W$, again by quotient uniqueness. This proves the required isomorphism over $T$ and
   object descent.
10. Fix finitely presented $Y_i,Z_i$ over $T_i$ and a $T$-map $\alpha:Y\to Z$ of their
   pullbacks. By [lem-sfb-space-fp-qcqs-source], $Y_i$ is qcqs. Choose an affine surjective
   etale atlas $W_i\to Y_i$ by [lem-sfb-qc-space-affine-etale-atlas]. By
   [lem-a1-etale-atlas-presentation] its kernel pair $R_i$ is a scheme and $Y_i=W_i/R_i$. The
   scheme $W_i$ is qcqs by [lem-weil-pbc-affine-scheme-qcqs]; then
   [lem-sfb-qcqs-space-fibre-product] makes $R_i$ qcqs. Put $W_k=W_i\times_{T_i}T_k$ and
   $R_k=R_i\times_{T_i}T_k$. By [lem-weil-pbc-scheme-over-limit] these systems have affine
   transitions and limits $W,R$. Their maps to $W_i,R_i$ are affine by
   [lem-weil-pbc-affine-morphism-permanence](1), so its (3) and
   [lem-weil-pbc-qcqs-morphism-permanence](2) make every stage qcqs. Apply
   [lem-sfb-lfp-space-scheme-limit-test] over the fixed scheme $T_i$ with target $Z_i$ to $W\to
   Y\xrightarrow{\alpha}Z\to Z_i$. Since $Z_i\to T_i$ is locally finitely presented, this
   descends to $b_k:W_k\to Z_i$ at some $k\ge i$.
11. The maps $b_ks_k,b_kt_k:R_k\to Z_i$ agree after pullback to $R$. Apply the injectivity
   clause of [lem-sfb-lfp-space-scheme-limit-test] to the qcqs scheme system $(R_l)_{l\ge k}$ to
   make them equal at a later stage $l$. Pair $b_l$ with the structure map into $T_l$ to obtain
   a $T_l$-map $W_l\to Z_l$, equalizing $R_l\rightrightarrows W_l$. By
   [lem-trf-space-fibre-products-etale-covers], this is the kernel pair of the pullback atlas
   $W_l\to Y_l$. By [lem-a1-etale-atlas-presentation] and [lem-trf-etale-relation-quotient], the
   equalizing map factors uniquely through $\alpha_l:Y_l\to Z_l$. It respects $T_l$ because its
   composite to $T_l$ and the structure map of $Y_l$ agree after $W_l\to Y_l$, so quotient
   uniqueness makes them equal. Its base change is $\alpha$, since both maps agree on $W$. Thus
   every morphism descends; the scheme $R_l$ need not be affine.
12. For two stage maps $a_i,b_i:Y_i\to Z_i$ whose pullbacks agree, restrict them to the affine
   atlas $W_i\to Y_i$ from step 10. Injectivity in [lem-sfb-lfp-space-scheme-limit-test] makes
   these two maps $W_i\to Z_i$ equal after some base change $T_l\to T_i$. The pulled-back atlas
   presents $Y_l$ as $W_l/R_l$ by [lem-trf-space-fibre-products-etale-covers] and
   [lem-a1-etale-atlas-presentation]. Quotient uniqueness [lem-trf-etale-relation-quotient]
   therefore makes $a_l=b_l$. If the maps start at different stages, first move them to a common
   stage by directedness. This is precisely the eventual-equality assertion. All three
   conclusions were obtained for qcqs, possibly nonaffine stage bases.
-/
theorem fp_space_qcqs_base_limit_descent
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i).left]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i).left]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit c) :
    (∀ (Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
      (f : Y.obj.obj ⟶ yoneda.obj c.pt),
      MapToSchemeIsLocally (@LocallyOfFinitePresentation) Y c.pt f →
      MapIsQuasiCompact f → MapIsQuasiCompact (pullback.diagonal f) →
      ∃ (i : I) (Yi : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
        (fi : Yi.obj.obj ⟶ yoneda.obj (D.obj (op i))),
        MapToSchemeIsLocally (@LocallyOfFinitePresentation) Yi (D.obj (op i)) fi ∧
        MapIsQuasiCompact fi ∧ MapIsQuasiCompact (pullback.diagonal fi) ∧
        Nonempty ((Over.pullback (yoneda.map (c.π.app (op i)))).obj (Over.mk fi) ≅
          Over.mk f)) ∧
    (∀ (i : I) (Y Z : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
      (f : Y.obj.obj ⟶ yoneda.obj (D.obj (op i)))
      (g : Z.obj.obj ⟶ yoneda.obj (D.obj (op i))),
      MapToSchemeIsLocally (@LocallyOfFinitePresentation) Y (D.obj (op i)) f →
      MapIsQuasiCompact f → MapIsQuasiCompact (pullback.diagonal f) →
      MapToSchemeIsLocally (@LocallyOfFinitePresentation) Z (D.obj (op i)) g →
      MapIsQuasiCompact g → MapIsQuasiCompact (pullback.diagonal g) →
      ∀ α : (Over.pullback (yoneda.map (c.π.app (op i)))).obj (Over.mk f) ⟶
        (Over.pullback (yoneda.map (c.π.app (op i)))).obj (Over.mk g),
      ∃ (j : I) (h : i ≤ j)
        (β : (Over.pullback (yoneda.map (D.map (homOfLE h).op))).obj (Over.mk f) ⟶
          (Over.pullback (yoneda.map (D.map (homOfLE h).op))).obj (Over.mk g)),
        α =
          eqToHom (congrArg (fun a ↦ (Over.pullback a).obj (Over.mk f))
            (((yoneda.map_comp _ _).symm.trans
              (congrArg yoneda.map (c.w (homOfLE h).op))).symm)) ≫
          (Over.pullbackComp (yoneda.map (c.π.app (op j)))
            (yoneda.map (D.map (homOfLE h).op))).hom.app (Over.mk f) ≫
          (Over.pullback (yoneda.map (c.π.app (op j)))).map β ≫
          (Over.pullbackComp (yoneda.map (c.π.app (op j)))
            (yoneda.map (D.map (homOfLE h).op))).inv.app (Over.mk g) ≫
          eqToHom (congrArg (fun a ↦ (Over.pullback a).obj (Over.mk g))
            ((yoneda.map_comp _ _).symm.trans
              (congrArg yoneda.map (c.w (homOfLE h).op))))) ∧
    (∀ (i : I) (Y Z : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
      (f : Y.obj.obj ⟶ yoneda.obj (D.obj (op i)))
      (g : Z.obj.obj ⟶ yoneda.obj (D.obj (op i))),
      MapToSchemeIsLocally (@LocallyOfFinitePresentation) Y (D.obj (op i)) f →
      MapIsQuasiCompact f → MapIsQuasiCompact (pullback.diagonal f) →
      MapToSchemeIsLocally (@LocallyOfFinitePresentation) Z (D.obj (op i)) g →
      MapIsQuasiCompact g → MapIsQuasiCompact (pullback.diagonal g) →
      ∀ α β : Over.mk f ⟶ Over.mk g,
        (Over.pullback (yoneda.map (c.π.app (op i)))).map α =
          (Over.pullback (yoneda.map (c.π.app (op i)))).map β →
        ∃ (j : I) (h : i ≤ j),
          (Over.pullback (yoneda.map (D.map (homOfLE h).op))).map α =
            (Over.pullback (yoneda.map (D.map (homOfLE h).op))).map β) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
