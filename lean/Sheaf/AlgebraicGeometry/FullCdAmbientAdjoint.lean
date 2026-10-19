/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint
import Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
import Sheaf.AlgebraicGeometry.ProEtaleModuleDirectImageLeftExact
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Sheaf.CategoryTheory.KInjectiveComputes
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Paper.CondensedQcqsPushforwardContinuity
import Sheaf.Paper.ProfinitePointPullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
import Sheaf.AlgebraicGeometry.ProperOpenSection
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Compactification.CategoryBaseChange
import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.AlgebraicGeometry.ClopenSectionComponent
import Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport
import Sheaf.Paper.FiniteDirectImageComposition
import Sheaf.Paper.RingedProjectionRestriction
import Sheaf.Paper.SfCommonStageDirectImage
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

/-! # Full cohomological dimension and the ambient exceptional adjoint

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-existence`, clause (b)
(blueprint: lem-sp-fullcd-ambient-adjoint).

This is the conditional statement on the ordinary unbounded small pro-etale derived
categories. It asserts no FullCD bound for a general proper morphism.
-/

@[expose] public section

set_option autoImplicit false

universe w u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A FullCD bound for the chosen proper part makes its compact-support candidate preserve
set-indexed coproducts and gives the coherent ambient exceptional right adjoint datum.
The datum supplies an adjunction at every compactification, including the distinguished
one, and natural refinement comparisons satisfying the unit, counit and cocycle equations.
The finite coefficient instance is supplied by the recorded positive-level finiteness
statement, without adding a hypothesis or choosing another coefficient ring.

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-existence`, clause (b);
Stacks Project, Tag 0F5Y, for the Brown representability step only
(blueprint: lem-sp-fullcd-ambient-adjoint).

Proof in words (the ten steps of the node):
1. Write $\mathsf M_T=\operatorname{Mod}(A_T)$. By [lem-pur-ringed-site-grothendieck-abelian]
   these are Grothendieck abelian categories, using the small-site universe fixed in
   [def-weil-pbc-proetale-site]. By [lem-weil-proetale-module-direct-image-left-exact], $p_*$ is
   additive and left exact. The first clause of [def-weil-full-cohomological-dimension] says
   $R^qp_*F=0$ for every sheaf $F$ and $q>c$; classical derived functors agree here with
   cohomology of the total derived image on a sheaf, by [lem-sp-kinjective-computes](2), applied
   to the finite-level construction [def-weil-derived-direct-image]. This uses sheaves on the
   entire source, not just those of etale origin. Properness makes $p$ qcqs. For every
   compactification $d=(j_d,p_d)$ the open $j_d$ is quasi-compact by
   [lemma-nagata-open-immersion-qc-over-separated-target], applied with base $Y$, source $X$ of
   finite type over $Y$, and separated target $\overline X_d\to Y$. The scheme $\overline X$ is
   finite type over $S$: $p$ is finite type by properness, and finite affine covers with finite
   lists of algebra generators compose with those for $Y\to S$. Thus the stated FullCD definition
   applies to this proper part.
2. Use the existing [lem-weil-pbc-condensed-qcqs-pushforward-continuity] with the constant
   condensed ring $\underline A$ on profinite sets and complexes in degree zero. Its coefficient
   sheaf is exactly $A_T$: the functors $p_T^*$ in [lem-weil-pbc-profinite-point-pullback] are
   geometric inverse images, so preserve copowers of the terminal sheaf, hence constant sheaves
   and their ring operations as defined in [def-weil-pbc-constant-sheaf]. Their composition
   comparisons identify $p^{-1}A_Y$ with $A_{\overline X}$. For a family $(M_i)_{i\in I}$, index
   by the filtered poset of finite subsets $J\subset I$, and set $K_J=(\bigoplus_{i\in J}M_i)[0]$.
   These complexes have common lower bound zero, and their termwise filtered colimit is
   $(\bigoplus_{i\in I}M_i)[0]$, by the coproduct universal property. The cited continuity theorem
   gives $\varinjlim_J R^qp_*(\bigoplus_{i\in J}M_i)\cong R^qp_*(\bigoplus_iM_i)$, using the
   classical/total identification from step 1. The classical functors are additive: a finite sum
   of injective resolutions is an injective resolution of the finite sum, since finite biproducts
   of injectives are injective and finite sums are exact; applying the additive $p_*$ and taking
   cohomology preserves that finite biproduct. Thus the left side is $\bigoplus_i R^qp_*M_i$, with
   its canonical coprojections. This proves preservation of sums for every $q\geq0$, including
   $p_*=R^0p_*$. For injective sheaves $J_i$, [lem-weil-pbc-derived-functor-injective-vanishing]
   now gives $R^qp_*(\bigoplus_iJ_i)=\bigoplus_i R^qp_*J_i=0$ for $q>0$: sums of injectives are
   $p_*$-acyclic. The empty family uses the same argument, since the finite-subset poset then has
   the single object $\varnothing$.
3. Given arbitrary unbounded complexes $(K_i)$, choose K-injective resolutions $K_i\to I_i$ with
   each term of $I_i$ injective, by [lem-pur-kinjective-degreewise-existence]. Their termwise sum
   represents the derived coproduct, by [lem-kun-grothendieck-derived-coproducts].
   Filtered-colimit exactness in the Grothendieck category makes direct sums exact (write a sum as
   the filtered union of finite sums); hence $\bigoplus_iK_i\to\bigoplus_iI_i$ is a
   quasi-isomorphism. Every term of $\bigoplus_iI_i$ is $p_*$-acyclic by step 2. Apply
   [lem-kun-finite-cd-acyclic-complex] with bound $c$ from step 1, both to each $I_i$ and to their
   sum. It identifies $Rp_*I_i$ with $p_*I_i$ and $Rp_*(\bigoplus_i I_i)$ with
   $p_*(\bigoplus_iI_i)$. The latter is termwise $\bigoplus_i p_*I_i$ by step 2. Naturality of the
   acyclic-complex comparison identifies these isomorphisms on every coprojection, so the map
   proved invertible is exactly $\bigoplus_i Rp_*K_i\to Rp_*(\bigoplus_iK_i)$. The same
   calculation covers the empty family.
4. By [prop-exc-open-adjoint], the derived $j_!$ is a left adjoint on all the ordinary derived
   categories. It preserves every coproduct: for any $L$, adjunction identifies
   $\operatorname{Hom}(j_!(\bigoplus_iK_i),L)$ with
   $\operatorname{Hom}(\bigoplus_iK_i,j^*L)=\prod_i\operatorname{Hom}(K_i,j^*L)
   =\prod_i\operatorname{Hom}(j_!K_i,L)$,
   with the indicated coprojections. Consequently $F_c=Rp_*j_!$ preserves all set-indexed
   coproducts by step 3. It is exact: the termwise $j_!$ is triangulated by
   [lem-weil-extension-by-zero-exact, lem-sf-exact-functor-derived-triangulated], and the
   unbounded $Rp_*$ is triangulated by [lem-pc-right-derived-functor-triangulated]. Composing
   these shift and triangle identifications gives those for $F_c$.
5. Apply [lem-grothendieck-derived-brown-right-adjoint] to the Grothendieck category $\mathsf M_X$
   and to the exact coproduct-preserving functor $F_c:D(\mathsf M_X)\to D(\mathsf M_Y)$ of step 4.
   It supplies a right adjoint $G_c$ and natural bijections
   $\Phi^c_{K,L}:\operatorname{Hom}(F_cK,L)\cong\operatorname{Hom}(K,G_cL)$. Denote $G_c$ by
   $Rf_n^\times$. Brown is applied to the full unbounded source in a common indexing universe,
   without any compact-generation or constructibility premise.
6. For a refinement $u:d\to e$, put $V=\overline X_d\times_{\overline X_e}X$, with open
   $b:V\to\overline X_d$, projection $q:V\to X$, and the section $s:X\to V$ induced by $j_d$. By
   [lem-weil-pbc-proper-open-section], $s$ identifies $X$ with an open-and-closed component of $V$
   and $qs=1$. There is a canonical open-restriction isomorphism $j_e^*Ru_*N\cong Rq_*b^*N$ on
   unbounded inputs. Here is its construction, not an invocation of an etale comparison: choose a
   K-injective resolution $N\to I$ using [lem-pur-kinjective-degreewise-existence]; restriction to
   an open preserves K-injectivity, since for any acyclic $C$ its Hom into $b^*I$ is the Hom of
   $b_!C$ into $I$, which is zero by exactness of $b_!$ and [def-pur-kinjective-complex]. The
   sheaf adjunction [lem-weil-extension-by-zero-adjunction] extends termwise to chain maps and
   homotopies, and [lem-weil-extension-by-zero-exact] makes its left adjoint preserve acyclic
   complexes. Open restriction is exact by [def-weil-pbc-proetale-operations]; its interpretation
   as restriction of the localized site is [lem-weil-proetale-weakly-etale-localization]. The
   section formula [def-weil-proetale-module-direct-image] identifies $j_e^*u_*I$ with $q_*b^*I$
   termwise. The computation on K-injectives [lem-weil-pbc-kinjective-total-derived] gives the
   asserted comparison. Applied to $N=j_{d!}K$, the Cartesian open square with sides $j_d,b,s,1_X$
   gives $b^*j_{d!}K=s_!K$ by [lem-cbc-proetale-extension-zero-base-change]. Here the component
   calculation is explicit: for every site object $W\to V$, its two inverse-image opens over $sX$
   and $V\setminus sX$ cover $W$ with empty overlap. The sheaf axiom identifies its sections with
   the product of the sections on those two opens. Restriction and gluing therefore identify
   module sheaves, complexes and chain homotopies on $V$ with pairs on those components; exactness
   is componentwise, and $s_!K$ is $(K,0)$ by its defining extension presheaf. For an acyclic pair
   $(C_1,C_2)$, maps into $(I,0)$ are exactly maps $C_1\to I$ and hence null-homotopic when $I$ is
   K-injective on $X$. Thus $(I,0)$ is K-injective on $V$. The direct-image section formula gives
   $(q_*s_!I)(W)=I(W)$ for $W\to X$, since $qs=1$ and the complementary component contributes
   zero. We obtain a natural isomorphism $\lambda_u:j_e^*Ru_*j_{d!}K\cong K$, normalized by
   restriction to this component.
7. By [lem-sp-proper-open-derived-support], the counit $j_{e!}j_e^*M\to M$, $M=Ru_*j_{d!}K$, is
   invertible; the quasi-compactness assumptions were checked in step 1. Define
   $\alpha_u:j_{e!}K\to Ru_*j_{d!}K$ as this counit after $j_{e!}(\lambda_u^{-1})$. It is a
   natural isomorphism. This is precisely where ambient proper support is needed: neither the
   etale-only comparison nor the bounded-below etale-origin comparison supplies this counit on
   arbitrary $K$. Also the presheaf defining $j_{e!}M$ in [def-weil-extension-by-zero], restricted
   to the localized site of [lem-weil-proetale-weakly-etale-localization], is exactly $M$; it is
   already a sheaf there. Thus the open-adjunction unit $M\to j_e^*j_{e!}M$ is the identity
   identification, termwise and hence on derived categories. In combination with
   [prop-exc-open-adjoint] it gives $\operatorname{Hom}(j_{e!}K,j_{e!}L)=\operatorname{Hom}(K,L)$,
   so extension is fully faithful. Maps between these supported objects are therefore determined
   by restriction to $X$.
8. For the identity refinement, $\alpha_1$ is the identity under the identity direct-image
   comparison, since its restriction is $1_K$. For composable refinements $u:d\to e$, $v:e\to h$,
   compare $\alpha_{vu}$ with $Rv_*(\alpha_u)\circ\alpha_v$, using the canonical $R(vu)_*\cong
   Rv_*Ru_*$ of [lem-weil-derived-direct-image-composition]. They are equal: both source and
   target are supported on $j_hX$ by step 7 (the target identifies with $R(vu)_*j_{d!}K$), and
   restricting to $X$ gives the identity under $\lambda_{vu}$. To check that normalization, take a
   K-injective resolution on $\overline X_d$. Direct image preserves K-injectives by
   [lem-weil-pbc-right-adjoint-preserves-kinjective], applied to its exact inverse-image left
   adjoint in [def-weil-pbc-proetale-operations], and open restriction preserves them by step 6.
   Thus the successive direct images and restrictions are computed on this common model: every
   open restriction is literal restriction of sections, the component $X$ is the same component in
   the iterated fibre product, and both composites there are $1_K$; the associativity
   normalization of the cited composition isomorphism identifies the two models. Thus, writing the
   composition comparison implicitly, $\lambda_{vu}\circ
   j_h^*(Rv_*\alpha_u\circ\alpha_v)=1_K=\lambda_{vu}\circ j_h^*\alpha_{vu}$; here naturality of
   restriction on sections gives the first equality. Full faithfulness from step 7 gives equality
   before restriction. Thus the proper/open comparisons satisfy identity and composition
   equations, as actual maps rather than merely unspecified isomorphisms.
9. For $u:d\to e$, proper composition and step 7 give $F_d=R(p_d)_*j_{d!}\cong
   R(p_e)_*Ru_*j_{d!}\xrightarrow{R(p_e)_*\alpha_u^{-1}}R(p_e)_*j_{e!}=F_e$; call the composite
   $\theta_u$. By [lem-weil-derived-direct-image-composition] and step 8, $\theta_1=1$ and
   $\theta_{vu}=\theta_v\theta_u$. The category of compactifications is cofiltered by
   [lem-cbc-compactifiable-cofiltered], applicable because $f$ is separated finite type, has the
   given compactification, and its open is quasi-compact by step 1. Hence for any $d,e$ choose a
   common refinement $r$ with arrows $a:r\to d$, $b:r\to e$ and set
   $\theta_{d,e}=\theta_b\theta_a^{-1}$. For two such choices, choose a further common refinement
   and then equalize the two resulting parallel arrows to $d$ and to $e$; functoriality of the
   $\theta_u$ makes the two expressions equal after cancelling the invertible maps from that
   further refinement. Thus the comparison is independent of the choice. For three objects,
   compute through one common refinement and cancel the map to the middle object:
   $\theta_{e,h}\theta_{d,e}=\theta_{d,h}$. These comparisons agree with those of individual
   refinements.
10. Fix the chosen compactification, denoted $c$ in the following comparison formulas (distinct
   from the integer bound), and abbreviate $t_d=\theta_{d,c}:F_d\cong F_c$, so $t_c=1$ and
   $t_d=t_e\theta_u$ for $u:d\to e$. Define $G_d=G_c$ for every $d$, and $\Phi^d(h)=\Phi^c(h\circ
   t_{d,K}^{-1})$. These are natural bijections, hence give adjunctions by
   [lem-weil-pbc-adjunction-of-natural-bijection]. Their units and counits are explicitly
   $\eta^d_K=G_c(t_{d,K}^{-1})\eta^c_K$ and $\varepsilon^d_L=\varepsilon^c_L\,t_{d,G_cL}$. Set
   every right-adjoint comparison $\rho_u:G_e\to G_d$ equal to $1_{G_c}$. From $t_d=t_e\theta_u$
   we get $t_e^{-1}=\theta_u t_d^{-1}$, hence $\eta^e_K=G_c(\theta_{u,K})\eta^d_K$ and
   $\varepsilon^d_L=\varepsilon^e_L\theta_{u,G_cL}$. These are exactly the two compatibility
   equations in [def-weil-ambient-exceptional-adjoint], with $\rho_u=1$. Identity and composite
   comparisons for the right adjoints are identities, while those for the left adjoints were
   checked in step 9. Together with the given integer $c$ and its FullCD condition, this
   constructs every component of the stated ambient datum.
-/
theorem sfAmbientCompactSupport_preservesCoproducts_and_hasAmbientDatum_of_fullCD
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x))
    [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
    (f : X ⟶ Y) [f.IsOver S] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (d : Compactification f) (c : ℕ)
    (hcd : sfFullCohomologicalDimension d.g (Padic.coefficientExtensionRing l E n) c) :
    (∀ I : Type w, PreservesColimitsOfShape (Discrete I)
      (@sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E n) _
        (Padic.finite_coefficientExtensionRing l E n hn) X Y f d)) ∧
      HasAmbientExceptionalRightAdjointDatum l E n hn S X Y hS f d := by
  sorry

end AlgebraicGeometry.Scheme
