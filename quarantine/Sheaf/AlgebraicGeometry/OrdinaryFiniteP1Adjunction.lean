/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Mathlib.Topology.Defs.Filter
import Sheaf.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import Sheaf.AlgebraicGeometry.Curve.PicardDecomposition
import Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Sheaf.AlgebraicGeometry.SecondKummerDivisors
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.Curve.Estimate
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension

/-!
# Ordinary etale projective-line adjunction for finite coefficients

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/thm-amb-p1-adjunction.md,
thm-amb-p1-decomposition.md and def-amb-p1-trace.md; Stacks Project, Tag 03PL
(blueprint: lem-asd-ordinary-finite-p1-adjunction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Ordinary etale projective-line duality, with the scalar-extended Kummer class,
normalized trace and actual counit, on the entire derived categories. The chosen
transport is fixed by its roots-of-unity and pure-tensor normalizations; the
record's counit equation uses precisely the ordered projection map.
Source: blueprint thm-amb-p1-adjunction, thm-amb-p1-decomposition,
and def-amb-p1-trace; Stacks Project, Tag 03PL
(blueprint: lem-asd-ordinary-finite-p1-adjunction).

Proof plan, following the DAG node:

1. Put $R=\mathbf Z/N$. Work throughout on ordinary small etale sites. Both coefficient rings to
   which the projection theorem is applied are finite commutative rings: $R=\mathbf Z/N$ is
   finite and $A$ is finite by hypothesis. Its $r^*$ is exactly the termwise inverse image
   $r^{-1}$ used here. In all steps below, the ordered projection map is the symmetry-conjugate
   of the adjoint-of-counit map, exactly as specified in [lem-amb-proper-coproducts-projection];
   thus the inverse in the stated counit uses this specified map. The projections $q:P\to S$ and
   $p_a:P\times_SP\to P$ are projective-line projections, hence proper by
   [lemma-nagata-projective-space-base-change-proper]. They have finite type and Noetherian
   sources, so the arbitrary-complex projection formula of
   [lem-amb-proper-coproducts-projection] applies. The standard opens of
   $\operatorname{Proj}\mathbf Z[x_0,x_1]$ are supplied by [def-nagata-affine-proj]. Their
   degree-zero rings are $\mathbf Z[x_1/x_0]$ and $\mathbf Z[x_0/x_1]$: every degree-zero
   monomial fraction is a power of the indicated ratio, and those powers are independent. Pull
   back this cover through the base-change definition of $P$. By
   [lem-weil-pbc-fibre-product-affine-spectra], tensoring these rings with $B$ gives $B[t]$ and
   $B[s]$. Explicitly over each affine Noetherian open of $S$, the two charts are
   $\operatorname{Spec}B[t]$ and $\operatorname{Spec}B[s]$; their product charts are
   $\operatorname{Spec}B[t,u]$. [pqf-lem-locnoeth-lft] makes these finite-type sources locally
   Noetherian; the finite charts over the finite affine cover of the Noetherian base make them
   quasi-compact, hence Noetherian. The diagonal is closed because $q$ is separated (part of
   properness); [lem-weil-pbc-closed-immersion-proper](a) makes it proper and of finite type.
   Every exchange needed below is invertible on the entire derived category by
   [lem-kun-proper-base-change-torsion-ring], with $R$ or $A$: both are killed by $N$. The
   twist-line lemma [lem-asd-finite-etale-twist-line] makes $R_T(1)=\mu_{N,T}$ locally free of
   rank one over $R_T$, and makes $A_T(1)$ locally free of rank one over $A_T$. In particular
   the twists are flat. Pullback preserves their equations and their scalar-extension
   description. None of this uses an adic twist.

2. First prove the decomposition over $R$. At a geometric point $\bar s=\operatorname{Spec}k\to
   S$, with $k$ algebraically closed, the fibre is $\mathbf P^1_k$. By
   [lem-asd-projective-line-genus-zero] it is a smooth proper connected curve of genus zero.
   Choose a primitive $N$th root using [lem-sc-primitive-root]. Apply [thm-sc-proper-cohomology]
   with $g=0$: the constant $R$-cohomology is $R$ in degrees $0,2$ and zero otherwise. The
   primitive root identifies $\mu_N$ with that constant sheaf, so the same vanishing holds for
   $\mu_N$, with $H^0=\mu_N(k)$. To check the degree-two component rather than just its rank,
   [lem-sc-second-kummer-divisors] identifies $H^2(P_k,\mu_N)$ with $\operatorname{Pic}(P_k)/N$
   by the actual Kummer boundary. The split degree sequence [lem-sc-pic-proper-decomposition]
   and $N$-divisibility of $\operatorname{Pic}^0$ from [lem-sc-pic-proper-ntorsion] identify
   this quotient with $\mathbf Z/N$ by degree. The divisor $x_1=0$ is one $k$-rational point.
   Its ideal generators on $D(x_0)$ and $D(x_1)$ are $t=x_1/x_0$ and $1$; their dual generators
   satisfy $g_0=t^{-1}g_1$, so its line bundle is the specified $\mathcal O(1)$. Its degree is
   one by [def-sc-pic0]. Thus $h_R$ induces the isomorphism $R\to H^2(P_k,\mu_N)$ taking $1$ to
   degree one. The twisted shifted unit induces the identity on $H^0(P_k,\mu_N)$. Proper
   exchange [lem-kun-proper-base-change-torsion-ring] gives these computations on the geometric
   stalks of the cohomology of $b_{q,R}$. Exactness of stalks
   [prop-weil-pbc-geometric-stalks-exact] and [lemma-weil-pbc-geometric-stalk-conservative] make
   every cohomology map invertible. The unbounded cohomology criterion
   [lem-weil-pbc-unbounded-derived-iso-cohomology] proves $b_{q,R}$ invertible.

3. Apply derived scalar extension $A\otimes_R^L-$ to $b_{q,R}$. To identify its target use the
   projection formula of [lem-amb-proper-coproducts-projection] with its finite coefficient ring
   specialized to $R=\mathbf Z/N$, with $K=A_S$ regarded as an $R$-module complex and
   $L=\mu_{N,P}[2]$. It gives $A_S\otimes_R^LRq_*\mu_{N,P}[2]\cong
   Rq_*(A_P\otimes_R^L\mu_{N,P})[2]$. The twist-line lemma makes $\mu_N$ flat, so
   $A_P\otimes_R^L\mu_{N,P}=A_P(1)$, even if $A$ is not $R$-flat. For precision construct the
   comparison inside $D(S_{\mathrm{et}},A)$ as follows, rather than trying to lift a morphism of
   $R$-complexes. Write $e_T^* = A_T\otimes_{R_T}^L-$ for the derived module pullback of the
   identity topos with ring map $R_T\to A_T$. The pullback tensor theorem
   [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] supplies these functors. Define the
   comparison $e_S^*Rq_{*,R}L\to Rq_{*,A}e_P^*L$ to be the adjunct of
   $$q_A^{-1}e_S^*Rq_{*,R}L\cong
   e_P^*q_R^{-1}Rq_{*,R}L\xrightarrow{e_P^*(\varepsilon_{q,R,L})}e_P^*L.$$ The canonical derived
   adjunctions and the projection-mate normalization are those of
   [lem-weil-pbc-ringed-projection-mate-exact]. Restriction of scalars is exact because kernels
   and cokernels are the same underlying sheaves. Its total derived functor is therefore
   termwise restriction by [lem-weil-pbc-exact-functor-derived-functor], and it reflects
   isomorphisms by the cohomology criterion [lem-weil-pbc-unbounded-derived-iso-cohomology]. The
   two factorizations $(P,A)\to(P,R)\to(S,R)$ and $(P,A)\to(S,A)\to(S,R)$ have the same
   structural ring map; [lem-weil-pbc-ringed-topoi-derived-pushforward-composition] identifies
   their derived direct images. Under this identification, the restriction of the displayed
   comparison is the $R$-projection map with $K=A_S$: both are adjunct to the same evaluation
   tensored with $A_P$. Here the ordered version is obtained by the two canonical tensor
   symmetries specified in the projection theorem; their naturality conjugates the usual
   counit-first mate into precisely this coefficient-first map. This can also be read as the
   tensor/exchange equality [lem-weil-pbc-ringed-exchange-tensor-coherence] for the commuting
   coefficient-change square of ringed topoi; that lemma explicitly does not require a Cartesian
   square of underlying topoi. Thus it is legitimate to test this $A$-linear comparison over
   $R$. On the source, scalar extension gives $A_S(1)[2]\oplus A_S$; naturality of the
   projection mate identifies its components with the shifted twisted unit and the
   scalar-extended Kummer class that defines $h$ in the item. Derived tensor preserves
   isomorphisms, hence the resulting map is exactly $b_q$ and is invertible.

4. Define $t_q=\operatorname{pr}_2b_q^{-1}$. Since $h=b_q\operatorname{in}_2$, $t_qh=1$ by
   cancellation. Under any change of Noetherian base $S'\to S$, the projective line and the line
   bundle with its displayed transition functions pull back to those over $S'$. Pullback of the
   equation $z^N=1$ identifies the twists, and the Kummer connecting homomorphism pulls back the
   class of the pulled-back line bundle, using [lem-amb-kummer-any-base]. The unit components
   correspond because exchange [def-kun-unbounded-exchange] is the mate of the inverse-image
   composition comparison: substituting its unit/counit formula on the unit of $q$ cancels the
   adjacent counit/unit by their triangle identity. The tensor comparison commutes with exchange
   by [lem-weil-pbc-ringed-exchange-tensor-coherence]. Consequently the square with $b_q$,
   $b_{q'}$ and the canonical proper exchange commutes. Inverting this square and composing with
   the second projection proves that $t_{q'}$ is the pullback of $t_q$. For arbitrary $K$ define
   $\epsilon_K$ by the displayed inverse projection formula followed by $1\otimes t_q$ and the
   tensor unit [lem-kun-tensor-unit]. Naturality gives a natural transformation $FG\to1$, where
   $F=Rq_*$, $G=q^{-1}(-)\otimes_A^LA_P(1)[2]$. The same tensor/exchange equality shows that
   these actual maps $\epsilon_K$, not merely their isomorphism classes, commute with base
   change.

5. Let $W=P\times_SP$ and $\Delta:P\to W$ be the diagonal. On the finite-finite chart its
   equation is $u-t$; on the infinity-infinity chart it is again a difference of coordinates; on
   a mixed chart it is $1-tu$. A monic difference is a non-zero-divisor over any base ring, and
   multiplication by $1-tu$ is injective by comparing the lowest total degree in a nonzero
   polynomial. Thus $\Delta$ is an effective Cartier divisor, and remains one after every base
   change here. Apply [lem-asd-ordinary-supported-kummer] to obtain $\delta:R\Delta_*A_P\to
   A_W(1)[2]$. Since $p_a\Delta=1_P$, derived pushforward composition
   [lem-weil-pbc-ringed-topoi-derived-pushforward-composition] gives $R(p_a)_*R\Delta_*A_P=A_P$.
   We claim $t_{p_a}R(p_a)_*\delta=1$ for both $a$. This is an endomorphism of the degree-zero
   sheaf $A_P$, so its equality with identity is an equality of sheaf morphisms. Subtract
   identity and take the image sheaf. By exactness of stalks
   [prop-weil-pbc-geometric-stalks-exact], if the difference is zero on every stalk its image
   has zero stalks. [lemma-weil-pbc-geometric-stalk-conservative] applied to
   $0\to\operatorname{im}(f-1)$ then makes the image zero, hence $f=1$. Proper exchange
   [lem-kun-proper-base-change-torsion-ring], supported Kummer base change and step 4 identify
   its geometric stalk with the integral of the supported class of one rational point of
   $\mathbf P^1_k$. Forgetting support gives that point's Kummer Chern class by the supported
   lemma. By [def-sc-pic0] its degree is one. The degree/Kummer identification in step 2
   therefore sends it to $1\in R$; scalar extension in step 3 sends it to $1\in A$, and
   projection onto the degree-two summand is exactly $t_{p_a}$. This proves both identities,
   including over disconnected or nonreduced bases. Only morphisms of degree-zero sheaves, not
   arbitrary derived morphisms, were tested for equality on stalks.

6. For $M\in D(P_{\mathrm{et}},A)$, projection for the proper closed immersion $\Delta$
   identifies $R\Delta_*A_P\otimes_A^Lp_1^{-1}M$ with $R\Delta_*M$, because
   $\Delta^{-1}p_1^{-1}M=M$. Define $$\eta_M:M\cong R(p_2)_*R\Delta_*M\longrightarrow
   R(p_2)_*(p_1^{-1}M\otimes_A^LA_W(1)[2])\cong q^{-1}Rq_*M\otimes_A^LA_P(1)[2].$$ The middle
   arrow uses $\delta\otimes1_M$ followed by the canonical tensor symmetry $A_W(1)[2]\otimes
   p_1^{-1}M\to p_1^{-1}M\otimes A_W(1)[2]$, using the preceding projection identification. This
   is the symmetry-conjugated ordered projection convention of step 1; the degree-two shift
   contributes sign $(-1)^{2i}=1$ on degree $i$ of $M$. For the last isomorphism, write
   $A_W(1)=p_2^{-1}A_P(1)$, apply the inverse projection formula for $p_2$, and then invert the
   canonical proper exchange $q^{-1}Rq_*M\to R(p_2)_*p_1^{-1}M$. These are isomorphisms on all
   complexes by [lem-amb-proper-coproducts-projection] and
   [lem-kun-proper-base-change-torsion-ring], not just on $D^+$. Pullback tensor comparisons are
   [lem-weil-pbc-ringed-topoi-derived-tensor-pullback], and the identity $R(p_2)_*R\Delta_*=1$
   is the composition comparison [lem-weil-pbc-ringed-topoi-derived-pushforward-composition].
   Every arrow is natural in $M$, so this defines $\eta:1\to GF$.

7. Check the first triangle $\epsilon_{FM}F\eta_M$. Use $qp_1=qp_2$, the direct-image
   composition comparison [lem-weil-pbc-ringed-topoi-derived-pushforward-composition], and the
   tensor/exchange equality [lem-weil-pbc-ringed-exchange-tensor-coherence]. They identify this
   composite with
   $$Rq_*M=R(qp_1)_*R\Delta_*M\xrightarrow{R(qp_1)_*(\delta\otimes1)}R(qp_1)_*(p_1^{-1}M\otimes
   A_W(1)[2])\cong Rq_*(M\otimes R(p_1)_*A_W(1)[2])\xrightarrow{Rq_*(1_M\otimes
   t_{p_1})}Rq_*M.$$ Here the trace on $p_1$ is the base change of $t_q$ by step 4. For the
   compatibility of these particular arrows, take the projection map to be the adjunct of the
   pullback tensor comparison followed by counit tensor identity, and exchange to be the adjunct
   of the square comparison followed by the pulled-back counit, as in
   [def-kun-unbounded-exchange]. In the two possible orders (exchange then projection,
   projection then exchange), their transposes are equal by the cited tensor/exchange coherence.
   For a composite pushforward the evaluation is $\varepsilon_{p_1}\circ p_1^{-1}\varepsilon_q$
   after pullback composition: substituting this into the projection mate gives the iterated
   projection, since naturality moves $\varepsilon_q$ past the intervening tensor comparison.
   This also explains the interchange of $qp_2$ and $qp_1$: both evaluate the same two
   coordinate pullbacks through their composite, with the square comparison inserted once.
   Naturality of the $p_1$ projection with respect to $\delta$ makes the middle map, after the
   first projection identification, $1_M\otimes R(p_1)_*\delta$. Thus the entire composite is
   $Rq_*(1_M\otimes(t_{p_1}R(p_1)_*\delta))$, which is $1_{FM}$ by step 5. This is an equality
   of derived morphisms proved by mates, not by stalkwise detection.

8. For the second triangle substitute $M=GK$ in step 6. The equality
   $p_1^{-1}q^{-1}K=p_2^{-1}q^{-1}K$ lets the $p_2$ projection formula take the common
   coefficient $q^{-1}K$ out of the pushforward. The canonical pullback tensor comparison
   [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] also identifies $p_1^{-1}A_P(1)$ and
   $p_2^{-1}A_P(1)$ with the one twist from $S$. Under these identifications, $\eta_{GK}$ is
   identity on $q^{-1}K\otimes A_P(1)[2]$ tensored with the arrow $R(p_2)_*\delta:A_P\to
   R(p_2)_*A_W(1)[2]$. The arrow $G\epsilon_K$ is identity on the same coefficient tensored with
   $t_{p_2}$: step 4 identifies this trace with $q^{-1}t_q$, and the tensor/exchange coherence
   [lem-weil-pbc-ringed-exchange-tensor-coherence] identifies its inverse projection with the
   one used in step 6. Cancelling these canonical inverse projection and exchange maps yields
   $$G\epsilon_K\,\eta_{GK}=1_{q^{-1}K\otimes A_P(1)[2]}\otimes(t_{p_2}R(p_2)_*\delta)=1_{GK}.$$
   The last equality is step 5. The interchange of the two copies of the unshifted twist is also
   identity: by [lem-asd-finite-etale-twist-line] it is locally free of rank one, and on a
   trivializing etale cover $ae\otimes be\mapsto be\otimes ae=ab(e\otimes e)$ by commutativity
   of $A$. Equality of these sheaf maps can be checked on that cover. Only shifts by $2$ are
   interchanged with tensor factors, so the Koszul factor is $(-1)^{2i}=1$ in every degree $i$
   of $K$. With both triangles proved, the Hom bijections are explicitly $a:FM\to K\mapsto
   G(a)\eta_M$ and $b:M\to GK\mapsto\epsilon_KF(b)$. Naturality and the two triangles show that
   their composites are identities. This constructs $F\dashv G$ with precisely the stated
   counit, for arbitrary unbounded $M,K$.

9. Finally the unit in step 6 commutes with a base change $S'\to S$: the diagonal equation pulls
   back to the diagonal equation; its supported Kummer class pulls back by
   [lem-asd-ordinary-supported-kummer]; the tensor/projection comparison commutes with exchange
   by [lem-weil-pbc-ringed-exchange-tensor-coherence]. The remaining proper exchanges paste
   canonically. To see this on maps, expand each exchange as the mate in
   [def-kun-unbounded-exchange]. In two successive squares substitute the composite evaluation
   $\varepsilon_v\circ v^{-1}\varepsilon_u$; naturality commutes the intermediate inverse-image
   comparison past $\varepsilon_u$, and the adjacent unit/evaluation cancels by the original
   pullback/direct-image triangle. The remaining transpose is exactly the outer square
   comparison followed by its pulled-back counit. The adjunction bijection therefore identifies
   the pasted exchange with the outer exchange, including for unbounded arguments. Thus the unit
   and the counit of step 4 pull back to the very unit and counit constructed over $S'$. Along
   with step 4 this proves compatibility of the decomposition, trace and normalized adjunction.
   When $N=1$, $A=0$ and all derived categories are zero, so all constructions give the unique
   adjunction and the assertions still hold; the empty base is equally harmless.
-/
theorem exists_ordinaryFiniteP1Adjunction (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    ∃ (t : OrdinaryFiniteTwistTransport A N hA)
      (d : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
        OrdinaryFiniteP1Datum A N hA t S hS), OrdinaryFiniteP1BaseChange A N hA t d := by
  sorry

end AlgebraicGeometry.Etale
