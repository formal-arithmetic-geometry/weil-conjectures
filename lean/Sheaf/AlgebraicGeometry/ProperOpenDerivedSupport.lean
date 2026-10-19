/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
import Sheaf.RingTheory.WContractibleClosedLocalization
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.AlgebraicGeometry.ProEtaleShriekSpecializationZero
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import Sheaf.Algebra.Homology.KInjectiveProducts
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Sheaf.CategoryTheory.SiteTruncationDerivedLimit
import Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageFormula
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic

/-!
# Proper direct image preserves open support on the full pro-etale derived category

Source: Weil blueprint, `sec-smooth-purity/sk-prop-sf-existence`, clause (b),
compactification independence (blueprint: lem-sp-proper-open-derived-support).
Stacks Project, Tag 09AG, supplies only the degree-zero specialization vanishing used
in the proof, rather than the full derived support assertion stated here.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The actual open-adjunction counit is invertible on the proper direct image of an
extension by zero, for every object of the ordinary unbounded derived category.

Source: Weil blueprint, `sec-smooth-purity/sk-prop-sf-existence`, clause (b),
compactification independence; the agent-extracted support obligation
(blueprint: lem-sp-proper-open-derived-support).

Proof in words (the ten steps of the node):
1. First prove the sheaf-level support assertion. Let $F$ be an $A_X$-module sheaf on
   $X_{\mathrm{proet}}$. Give $T_2\setminus j_2(X)$ its reduced induced closed subscheme
   $i_2:Z\hookrightarrow T_2$ using [lem-weil-pbc-reduced-induced-closed-subscheme]. Work over any
   affine open $O\subset T_2$. By [lem-exc-closed-inverse-image-formula], to show
   $i_2^*(u_*j_{1!}F)|_{Z\cap O}=0$ it suffices to show $(u_*j_{1!}F)(v(V))=0$ for every affine
   ind-etale basis object $V$ over $Z\cap O$. Indeed, the inverse image is the sheafification of
   these values. By [lem-weil-pbc-affine-closed-site-functor-properties], $W=v(V)$ is affine over
   $O$, $W\times_{T_2}Z=V$, and every point of $W$ specializes to a point of $V$. The same formula
   is valid on underlying abelian sheaves of our constant modules: the scalar action is simply
   retained under the inverse-image construction of [def-weil-pbc-proetale-operations]. Uses:
   lem-weil-pbc-reduced-induced-closed-subscheme, lem-exc-closed-inverse-image-formula,
   lem-weil-pbc-affine-closed-site-functor-properties, def-weil-pbc-proetale-operations.
2. Put $P=T_1\times_{T_2}W$ and $Z_P=P\times_{T_2}Z$. Every point $t\in P$ specializes to a point
   of $Z_P$. In fact the image of the closed subset $\overline{\{t\}}\subset P$ under $P\to W$ is
   closed, since $u$ is universally closed by [def-weil-proper-morphism]. It contains the image of
   $t$ and therefore a specialization of that image in $V$; a point of $\overline{\{t\}}$ over
   that specialization gives the required point of $Z_P$. Properness is preserved by
   [lem-weil-pbc-proper-base-change], so $P$ is quasi-compact and separated over the affine $W$.
   The complement of $Z_P$ is a quasi-compact open immersion, being the pullback of $j_2$ by
   [lem-pc-quasi-compact-base-change, lem-weil-pbc-open-immersion-base-change]. Uses:
   def-weil-proper-morphism, lem-weil-pbc-proper-base-change, lem-pc-quasi-compact-base-change,
   lem-weil-pbc-open-immersion-base-change.
3. Cover $Z_P$ by finitely many affine opens $P_a=\operatorname{Spec}R_a$ of $P$. Write $Z_P\cap
   P_a=V(I_a)$. Since its complementary open is quasi-compact, a finite principal-open subcover
   writes $V(I_a)=V(f_{a1},\ldots,f_{as_a})$ with $f_{ab}\in I_a$. By
   [lem-weil-pbc-wcontractible-closed-localization], $P_a^\sim=\operatorname{Spec}(S_a^{-1}R_a)$,
   where $S_a$ consists of elements invertible modulo $I_a$, has image exactly the points of $P_a$
   specializing to $Z_P\cap P_a$. Every point of $P$ specializes to a point of $Z_P$, hence is in
   some $P_a$ and in the image of $P_a^\sim$. These finitely many affine ind-Zariski maps are a
   pro-etale cover of $P$: on an affine open $Q$ of $P$, the intersection $P_a\cap Q$ is affine,
   since it is the pullback of the closed diagonal of $P\to W$ inside the affine $P_a\times_WQ$. A
   closed immersion is affine by [def-weil-closed-immersion], and closed immersions pull back by
   [lem-weil-pbc-closed-immersion-base-change]. The localization pullback to this intersection is
   affine too, so the inverse images of $Q$ are affine and jointly surjective. The same
   closed-base-change lemma makes $Z_P$ and its affine restrictions closed subschemes. Stability
   in [lem-weil-pbc-ind-etale-stability] and [def-weil-pbc-proetale-covering] justify the site
   claim. Viewed over $T_1$, each $P_a^\sim$ is affine weakly etale and all its points specialize
   to the closed inverse image of $Z$; this follows from the localization description and
   weakly-etale base-change/composition in that same stability lemma. That closed subscheme is
   disjoint from $j_1(X)$ because $uj_1=j_2$. Thus
   [lem-weil-pbc-proetale-shriek-specialization-zero] gives $(j_{1!}F)(P_a^\sim)=0$. The sheaf
   equalizer axiom makes $(j_{1!}F)(P)=0$. By the direct-image section formula in
   [def-weil-pbc-proetale-operations], this is $(u_*j_{1!}F)(W)=0$. Uses:
   lem-weil-pbc-wcontractible-closed-localization, lem-weil-pbc-ind-etale-stability,
   def-weil-pbc-proetale-covering, lem-weil-pbc-proetale-shriek-specialization-zero,
   def-weil-pbc-proetale-operations, lem-weil-pbc-closed-immersion-base-change,
   def-weil-closed-immersion.
4. Steps 1-3 show $i_2^*(u_*j_{1!}F)=0$. The exact sequence of
   [lem-weil-pbc-proetale-ringed-open-closed], applied on $T_2$ with $M_F=u_*j_{1!}F$, now reads
   $0\to j_{2!}j_2^*M_F\xrightarrow{\varepsilon}M_F\to0$. Its first arrow is the specified
   open-adjunction counit, so it is an isomorphism, naturally in every sheaf $F$. Notice that this
   argument uses neither geometric-stalk conservativity nor a higher-cohomology consequence of Tag
   09AG. Uses: lem-weil-pbc-proetale-ringed-open-closed.
5. Now let $K$ be bounded below. By [prop-pur-kinjective-resolutions-exist] the module categories
   on these small sites are Grothendieck abelian with enough injectives, and
   [lem-weil-pbc-dplus-injective-representative] supplies a bounded-below complex $J^\bullet$ of
   injective $A_X$-module sheaves representing $K$. Since $j_{1!}$ is exact
   [lem-weil-extension-by-zero-exact], $j_{1!}J^\bullet$ represents $j_{1!}K$. Apply
   [lem-sp-proetale-open-injective-proper-acyclic] to the square with $C=E=X$, $r=1_X$, $B=T_1$,
   $D=T_2$, $k=j_1$, $i=j_2$, $p=u$; identity is proper directly from its defining conditions. All
   open immersions are quasi-compact by hypothesis. Every term $j_{1!}J^a$ is $u_*$-acyclic. The
   bounded-below complexes clause of [lemma-weil-pbc-leray-acyclicity] consequently computes
   $M=Ru_*j_{1!}K$ by $u_*j_{1!}J^\bullet$. Step 4 makes the actual counit an isomorphism in every
   degree of this representing complex. Its localization is therefore exactly the derived counit
   $j_{2!}j_2^*M\to M$ of [prop-exc-open-adjoint], and is an isomorphism. Uses:
   prop-pur-kinjective-resolutions-exist, lem-weil-pbc-dplus-injective-representative,
   lem-weil-extension-by-zero-exact, lem-sp-proetale-open-injective-proper-acyclic,
   lemma-weil-pbc-leray-acyclicity, prop-exc-open-adjoint.
6. Here is the elementary sheaf-product argument, replacing a separate product lemma. For a
   quasi-compact open $j:U\hookrightarrow T$, choose its reduced closed complement
   $i:Z\hookrightarrow T$ by [lem-weil-pbc-reduced-induced-closed-subscheme]. Put $P=\prod_a
   j_!F_a$ for a countable family of constant-$A$ module sheaves. By
   [lem-weil-pbc-proetale-ringed-open-closed] and preservation of products by both immersion
   inverse images [lem-weil-pbc-proetale-immersion-limit-preservation], we have $i^*P=\prod_a
   i^*j_!F_a=0$ and $j^*P=\prod_a j^*j_!F_a\cong\prod_aF_a$. The same open-closed sequence
   therefore makes the counit $j_!j^*P\to P$ an isomorphism. Under the displayed identification
   its composite with each projection $P\to j_!F_a$ is $j_!$ of the corresponding projection, by
   naturality of the counit and the open unit $j^*j_!\cong1$. Thus it is precisely the canonical
   product comparison $j_!(\prod_aF_a)\to\prod_a j_!F_a$. This applies to $j=j_1$ and uses
   identified constant coefficient rings throughout. Uses:
   lem-weil-pbc-reduced-induced-closed-subscheme, lem-weil-pbc-proetale-ringed-open-closed,
   lem-weil-pbc-proetale-immersion-limit-preservation.
7. Countable products in pro-etale module categories are exact by
   [lem-weil-proetale-countable-products-exact]. By [lem-pc-ringed-space-product-kinjective],
   products of K-injective representatives represent derived products. Termwise products of
   arbitrary representing complexes also represent derived products: resolve each factor by a
   K-injective, take the product of the quasi-isomorphisms, and use exactness of products to see
   that its cone, the product of the acyclic cones, is acyclic. Thus an exact functor preserving
   countable sheaf products preserves countable derived products. Apply this to $j_{1!}$ using its
   product preservation proved in step 6 and [lem-weil-extension-by-zero-exact]. Also apply it to
   $i_2^*$: [lem-weil-pbc-proetale-immersion-limit-preservation] states both its exactness and its
   preservation of all sheaf limits for identified coefficient rings. Here the coefficients are
   constant $A$, with their canonical inverse-image identification. These exact functors induce
   triangulated functors by [lem-sf-exact-functor-derived-triangulated]. Uses:
   lem-weil-proetale-countable-products-exact, lem-pc-ringed-space-product-kinjective,
   lem-weil-extension-by-zero-exact, lem-sf-exact-functor-derived-triangulated,
   lem-weil-pbc-proetale-immersion-limit-preservation.
8. The functor $Ru_*$ is triangulated and right adjoint to exact inverse image by
   [def-weil-pbc-proetale-operations]. Hence it preserves countable derived products by
   [lem-weil-pbc-right-adjoint-preserves-limits]. Together with step 7, this says that
   $F=Ru_*j_{1!}$ and $i_2^*F$ are triangulated and preserve countable products. Recall
   [def-weil-derived-limit]: a tower $(N_n,t_n)$ has a homotopy-limit triangle
   $L\to\prod_nN_n\xrightarrow{1-s}\prod_nN_n\to L[1]$, where
   $\operatorname{pr}_ns=t_n\operatorname{pr}_{n+1}$. Applying $F$ preserves this triangle and,
   under its canonical product comparisons, preserves precisely $1-s$, since it preserves each
   projection and each transition. The same holds for $i_2^*$. We use only this triangle property;
   no uniqueness of a third arrow between triangles or of an arbitrary triangulated homotopy-limit
   comparison is assumed. Uses: def-weil-pbc-proetale-operations,
   lem-weil-pbc-right-adjoint-preserves-limits, def-weil-derived-limit.
9. For arbitrary $K$, put $K_n=\tau_{\geq-n}K$. Every pro-etale object has a cover by affine
   weakly contractible objects by [lem-weil-pbc-proetale-affine-wcontractible-covering-family]. On
   such an object evaluation is exact: a section of the target of a module epimorphism has locally
   a lift, the corresponding epimorphism of sheaves of lifts has a section by weak
   contractibility, and left exactness is the sheaf equalizer property. Hence $H^p(W,F)=0$ for
   $p>0$ and every module sheaf $F$, by applying the exact evaluation to an injective resolution.
   Apply [lem-kun-site-truncation-derived-limit] with this covering family and $d=0$. Its
   hypotheses hold for every negative cohomology sheaf of $K$, and it gives the triangle
   $K\to\prod_nK_n\xrightarrow{1-s}\prod_nK_n\to K[1]$. Thus the required lower-truncation
   homotopy limit is $K$ itself, with its canonical truncation maps. Uses:
   lem-weil-pbc-proetale-affine-wcontractible-covering-family,
   lem-kun-site-truncation-derived-limit.
10. For each $K_n$, step 5 gives $j_{2!}j_2^*F(K_n)\xrightarrow{\sim}F(K_n)$. The exact sheaf
   sequence in [lem-weil-pbc-proetale-ringed-open-closed] yields, on any representing complex $C$,
   a short exact sequence of complexes $0\to j_{2!}j_2^*C\to C\to i_{2*}i_2^*C\to0$. The closed
   counit $i_2^*i_{2*}\cong\operatorname{id}$ and $i_2^*j_{2!}=0$ are also in that cited
   statement. It follows that $i_2^*F(K_n)=0$. Apply $i_2^*F$ to the truncation triangle of step
   9. By step 8 its two product terms are products of these zero objects. The resulting triangle
   has the form $i_2^*F(K)\to0\to0\to i_2^*F(K)[1]$, whence $i_2^*F(K)=0$ by the exact Hom
   sequence. In the short exact sequence of complexes just displayed for a representative $C$ of
   $F(K)$, $i_2^*C$ is therefore acyclic. Exactness of $i_{2*}$, again stated by the cited ringed
   open-closed lemma, makes $i_{2*}i_2^*C$ acyclic. Thus its first arrow is a quasi-isomorphism.
   That arrow is termwise the specified open counit, so its localization is exactly
   $j_{2!}j_2^*Ru_*j_{1!}K\to Ru_*j_{1!}K$, as required. This identifies the actual counit,
   without using a possibly noncanonical isomorphism between homotopy limits. Uses:
   lem-weil-pbc-proetale-ringed-open-closed.
-/
theorem isIso_proper_open_derived_support
    {X T₁ T₂ : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [QuasiCompact j₁] [QuasiCompact j₂]
    (_comm : j₁ ≫ f = j₂) (A : Type u) [CommRing A] [Finite A]
    (K : proEtaleDerivedCategory X A) :
    IsIso ((exceptionalOpenAdjunction j₂ A).counit.app
      ((proEtaleConstantDerivedDirectImage f A).obj ((sfIntrinsicDerivedOpen A j₁).obj K))) := by
  sorry

end AlgebraicGeometry.Scheme
