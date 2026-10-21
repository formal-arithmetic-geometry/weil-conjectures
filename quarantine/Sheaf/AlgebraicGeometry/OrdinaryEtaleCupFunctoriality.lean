/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryEtaleCup
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.CategoryTheory.RingedToposMorphism
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.AlgebraicGeometry.CohomologyPullbackCanonicalArrows
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-! # Functoriality of ordinary etale cup products

Source: Stacks Project, Tags 0H9A and 0FPJ, Remark 0B6C.
(blueprint: lem-wf-etale-cup-functoriality)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- Ordinary integral cups commute with pullback and compatible coefficient maps.
No flatness, connectedness or invertibility hypothesis on the coefficients is imposed.
Source: Stacks Project, Tags 0H9A and 0FPJ.
(blueprint: lem-wf-etale-cup-functoriality)

Proof plan (the DAG proof, with its specified canonical comparisons):
1. Use the one-object point site with ring $\mathbf Z$, so its module category is $\mathrm{Ab}$.
For $T=X,Y$, take the global-sections geometric morphism $p_T:T_{\mathrm{Et}}\to\mathrm{pt}$,
with inverse image the constant-sheaf functor and structural ring map $p_T^{-1}\mathbf Z=\mathbf
Z_T$. The set-valued adjunction is [lem-weil-pbc-constant-sheaf-maps-global-sections]. Finite
limits are preserved: a finite tuple of locally constant sections is locally constant on a
common refinement, and equalizers impose the same equality locally. Thus this is a ringed-topos
morphism in [def-weil-pbc-ringed-topos-morphism]. On abelian groups the constant functor is
exact by [lem-weil-pbc-sheafification-exact], since constant presheaves are sectionwise exact.
The adjunction restricts to abelian groups by imposing addition and zero on both sides of its
natural bijection. Its right adjoint is $M\mapsto M(T)=\Gamma(T,M)$. Consequently $Rp_{T,*}$ on
a bounded-below complex $K$ is represented by $\Gamma(T,I)$ for a K-injective resolution $K\to
I$, exactly the $R\Gamma(T,K)$ of [def-weil-pbc-etale-cohomology]. The identifications on
morphisms also agree: both apply $\Gamma(T,-)$ to comparison maps of these same resolutions.
Work in a universe making the two etale sites small. No connectedness is assumed and the point
coefficient ring is $\mathbf Z$, not $\Gamma(T,\mathbf Z_T)$.
2. Put $A=Lp_X^*=p_X^{-1}$, $R=Rp_{X,*}$, $B=Lf^*=f^{-1}$, $S=Rf_*$, $C=Lp_Y^*=p_Y^{-1}$ and
$T=Rp_{Y,*}$. For $B$ the exactness and constant-ring identifications are [prop-weil-pbc-
inverse-image-modules-exact]; for $A,C$ use Step 1. Exact functors equal their termwise derived
functors by [lem-weil-pbc-exact-functor-derived-functor]. The generic ringed-topos lemma [lem-
weil-pbc-ringed-projection-mate-exact] gives the adjunctions $A\dashv R$, $B\dashv S$, $C\dashv
T$ and K-injective direct images. [lem-weil-pbc-ringed-topoi-derived-tensor-pullback], including
its specialization to the point site, supplies the derived tensors on the three module derived
categories and the natural comparisons $t_A,t_B,t_C$. Use unbounded derived categories
throughout; on bounded-below objects $R,T$ are those of Step 1. By [lem-sfb-ringed-derived-
monoidal-comparisons], the structural identification $p_Y\cong p_Xf$ gives monoidal $C\cong BA$
and adjunction-compatible $\kappa:T\xrightarrow{\sim}RS$. The structural 2-isomorphism is fixed
by the equality of underived section functors $\Gamma_X f_*=\Gamma_Y$ and their adjunction
bijections. In particular, under these comparisons,
$$t_C=t_B\circ B(t_A),\qquad
\varepsilon^Y_E=\varepsilon^f_E\circ B(\varepsilon^X_{SE}).$$
Here
$\varepsilon^X,\varepsilon^f,\varepsilon^Y$ denote the three counits. These formulas use the
composite-adjunction counit, not just an isomorphism of underlying functors.
3. Define $\beta_K=\kappa_{BK}^{-1}\circ R(\eta^f_K):RK\to TBK$, where $\eta^f:1\to SB$ is the
derived unit. This is natural in every derived morphism $K\to L$, since $\eta^f$ and $\kappa$
are natural. On bounded-below objects $\eta^f$ is the unit $\eta^D_f$ used in [lem-weil-pbc-
cohomology-pullback-derived-unit]: the canonical adjunction of [lem-weil-pbc-ringed-projection-
mate-exact] is induced by the underived adjunction $f^{-1}\dashv f_*$ with $B=f^{-1}$ exact and
$S$ computed by K-injective resolutions, so on a bounded-below complex $M$ with K-injective
resolution $f^{-1}M\to J$ its unit is the class of $M\to f_*f^{-1}M\to f_*J$, which is the
characterization of $\eta^D_f$ in that node's cited adjunction. For bounded-below arguments
$\beta$ is therefore the pullback of [lem-weil-pbc-cohomology-pullback-derived-unit]. To check
the comparison, let $E\to J$ be a bounded-below K-injective resolution on $Y$. Clause 1 of that
node says that $f_*J$ is K-injective. In the normalization of [lem-weil-pbc-ringed-topoi-
derived-pushforward-composition], choose the further resolution $f_*J\to f_*J$ to be the
identity. Then $\kappa_E$ is represented by the identity on $\Gamma(Y,J)=\Gamma(X,f_*J)$. The
Leray arrow $\lambda_E:RSE\to TE$ in the derived-unit node is represented by the same identity
in the opposite direction. Hence $\lambda=\kappa^{-1}$, including the canonical resolution
identifications, and clause 2 gives precisely $\beta$. This checks the direction of the
comparison rather than assuming that two unnamed Leray isomorphisms agree.
4. Define $\mu_X:RK\otimes^L RL\to R(K\otimes^L L)$ to be the adjoint of
$$m_X=(\varepsilon^X_K\otimes^L\varepsilon^X_L)\circ t_{A;RK,RL}:A(RK\otimes^L RL)\to K\otimes^L
L,$$
and define $\mu_Y$ with $C,T,\varepsilon^Y$. This is the relative cup construction of
Remark 0B6C, using the adjunction and tensor comparison of [lem-weil-pbc-ringed-projection-mate-
exact] and [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. In particular the defining
adjunction equation is
$$\varepsilon^X_{K\otimes^L L}\circ A(\mu_X)=m_X.$$
Both maps are natural
in both arguments. Explicitly for $u:U\to U'$, $v:V\to V'$ on $Y$, the mates of
$T(u\otimes^Lv)\mu_Y$ and $\mu_Y(Tu\otimes^LTv)$ are both
$(u\varepsilon^Y_U\otimes^Lv\varepsilon^Y_V)t_C$, by naturality of $t_C$ and of $\varepsilon^Y$.
Thus
$$T(u\otimes^Lv)\circ\mu_Y=\mu_Y\circ(Tu\otimes^LTv).$$
This proves the coefficient
naturality of the relative cup that will be needed below.
5. Compute the transpose of $\beta_K$, retaining the normalized comparisons of Steps 2–3. In the
following equation $C=BA$, $T=RS$ are identified by those comparisons. The composite-adjunction
counit of [lem-sfb-ringed-derived-monoidal-comparisons] gives
$$\begin{aligned}
\varepsilon^Y_{BK}\circ C(\beta_K)
&=\varepsilon^f_{BK}\circ B(\varepsilon^X_{SBK})\circ BA
R(\eta^f_K)\\
&=\varepsilon^f_{BK}\circ B(\eta^f_K)\circ B(\varepsilon^X_K)\\
&=B(\varepsilon^X_K).
\end{aligned}$$
The second equality is naturality of $\varepsilon^X$ for
the morphism $\eta^f_K:K\to SBK$. The last is the triangle identity $\varepsilon^f_{BK}\circ
B(\eta^f_K)=1_{BK}$ of the adjunction furnished by [lem-weil-pbc-ringed-projection-mate-exact].
This establishes the transpose formula from the actual unit and counits; it is not a clause
attributed to the additive pullback lemma.
6. We now prove the required derived square:
$$T(t_{B;K,L})\circ\beta_{K\otimes^L L}\circ\mu_X
=\mu_Y\circ(\beta_K\otimes^L\beta_L).$$
Take adjoints under $C\dashv T$. By Step 5, naturality
of $\varepsilon^Y$ and the defining equation of Step 4, the left-hand adjoint is
$$t_B\circ
B(\varepsilon^X_{K\otimes^L L})\circ BA(\mu_X)
=t_B\circ
B\bigl((\varepsilon^X_K\otimes^L\varepsilon^X_L)t_A\bigr)
=(B\varepsilon^X_K\otimes^LB\varepsilon^X_L)t_C.$$
The last equality uses naturality of $t_B$
and the monoidality of $C\cong BA$ in [lem-sfb-ringed-derived-monoidal-comparisons]. The right-
hand adjoint, by naturality of $t_C$, is
$$(\varepsilon^Y_{BK}\circ C\beta_K\ \otimes^L\
\varepsilon^Y_{BL}\circ C\beta_L)t_C
=(B\varepsilon^X_K\otimes^LB\varepsilon^X_L)t_C,$$
again by
Step 5. The adjunction bijection of [lem-weil-pbc-ringed-projection-mate-exact] is injective, so
the two derived morphisms agree. This fills the omitted square of 0H9A for the square with
vertical maps $p_X,p_Y$ and bottom map $\mathrm{id}_{\mathrm{pt}}$.
7. We also need to check the derived-to-underived tensor arrows, not just the square of Step 6.
For abelian sheaves $M,N$ on either etale site, choose functorial flat resolutions $P(M)\to
M[0]$, $P(N)\to N[0]$, zero in positive degrees, by [lem-pc-kflat-bounded-flat-replacement].
They are K-flat by [lem-pc-bounded-above-flat-kflat-site]. The canonical augmentation
$\delta_{M,N}:M\otimes^LN\to(M\otimes N)[0]$ is represented by the tensor of these two
augmentations. The total-tensor and derived-tensor identifications, with their naturality in
resolutions, are [def-pc-tensor-complex-sheaves] and [lem-weil-pbc-site-derived-tensor-descent].
Thus $\delta$ is natural in sheaf morphisms: on these functorial resolutions, both composites in
its naturality square are literally the tensor of the two augmented maps. For $B=f^{-1}$,
exactness [prop-weil-pbc-inverse-image-modules-exact] preserves the augmentations and [lem-weil-
pbc-ringed-topoi-derived-tensor-pullback] makes $BP(M),BP(N)$ valid K-flat models. On these
models $t_B$ is the termwise tensor identification of [lem-weil-pbc-ringed-topoi-module-
pullback-tensor]. Hence
$$\delta_{BM,BN}\circ t_{B;M,N}=q_{B;M,N}\circ B(\delta_{M,N}),$$
where
$q_B:B(M\otimes N)\xrightarrow{\sim}BM\otimes BN$ is that underived identification: the square
is the tensor of $BP(M)\to BM$ and $BP(N)\to BN$ in each bidegree.
8. The degree-zero normalization in Step 7 is the one in the hypothesis. Indeed a nonpositive
tensor total complex has degree-zero cokernel
$$\operatorname{coker}\bigl(P(M)^{-1}\otimes
P(N)^0\oplus P(M)^0\otimes P(N)^{-1}\to P(M)^0\otimes P(N)^0\bigr)=M\otimes N.$$
Tensor is right
exact in each variable: [lem-pc-sheaf-modules-tensor-closed] makes each tensor functor a left
adjoint, and [lem-weil-pbc-left-adjoint-preserves-colimits] applies to the finite cokernel
diagrams. Thus $H^0(\delta)$ is the displayed canonical isomorphism. Exactness of $B$ commutes
with these cokernels and cohomology by [prop-weil-pbc-inverse-image-modules-exact] and [lem-
weil-pbc-exact-functor-complex-cohomology]. The termwise formula in [lem-weil-pbc-ringed-topoi-
module-pullback-tensor] therefore identifies $H^0(t_B)$, under these $H^0(\delta)$ isomorphisms,
with $q_B$. In particular the coefficient hypothesis means exactly
$$c\circ
B(e)=e'\circ(a\otimes b)\circ q_{B;F,G}$$
as maps from $B(F\otimes G)$ to $H'$. No comparison
for scheme $\mathcal O$-modules is substituted for the constant-integer sheaf tensor.
9. Put $d=e\circ\delta_{F,G}:F\otimes^LG\to H$ and $d'=e'\circ\delta_{F',G'}$. Steps 7–8 and
naturality of $\delta$ give the equality of derived coefficient arrows
$$c\circ
B(d)=d'\circ(a\otimes^Lb)\circ t_{B;F,G}.$$
Combining this with Steps 3, 4 and 6 now gives, with
$T_a=T(a)\beta_F$ and similarly $T_b,T_c$,
$$\begin{aligned}
T_c\circ R(d)\circ\mu_X
&=T(c\circ
B(d))\circ\beta_{F\otimes^LG}\circ\mu_X\\
&=T(d')\circ T(a\otimes^Lb)\circ
T(t_B)\circ\beta_{F\otimes^LG}\circ\mu_X\\
&=T(d')\circ
T(a\otimes^Lb)\circ\mu_Y\circ(\beta_F\otimes^L\beta_G)\\
&=T(d')\circ\mu_Y\circ(T_a\otimes^LT_b).
\end{aligned}$$
The first equality uses naturality of
$\beta$ for $d$, not a claim of cup naturality from additive pullback naturality; the last is
the independently proved naturality of $\mu_Y$ in Step 4. This computation takes place in
unbounded derived categories, so no boundedness of $F\otimes^LG$ is assumed. Only $F,G,H$ need
the bounded-below pullback identification of Step 3.
10. Pass to the canonical cohomology pairing $H^p(U)\otimes H^q(V)\to H^{p+q}(U\otimes^LV)$ in
$D(\mathrm{Ab})$. For clarity, this pairing is natural: on K-flat resolutions of the already
derived complexes $U,V$ it sends cycles $z,w$ to the cycle $z\otimes w$; changing either cycle
by a boundary changes the result by a boundary by the signed total differential of [def-pc-
tensor-complex-sheaves], specialized to the point. Chain maps preserve this construction, and it
descends through the quasi-isomorphisms by [lem-weil-pbc-site-derived-tensor-descent], again on
the point site. These are resolutions of $R\Gamma_XF,R\Gamma_XG$, not ordinary global sections
of K-flat sheaf models. Apply this natural pairing and $H^{p+q}$ to Step 9. Under [def-weil-pbc-
etale-cohomology] and clause 2 of [lem-weil-pbc-cohomology-pullback-derived-unit],
$H^p(T_a)=H^p(Y,a)f^*$ and likewise for $b,c$. By the relative-cup definition in Step 4 followed
by $d,d'$, the resulting horizontal operations are precisely the $\smile_e,\smile_{e'}$ of the
statement. Evaluating the equality of Step 9 on $x,y$ proves
$$T_c^{p+q}(x\smile_e
y)=T_a^p(x)\smile_{e'}T_b^q(y).$$
11. For $f=\mathrm{id}$, use the identity-adjunction and identity-tensor clauses of [lem-sfb-
ringed-derived-monoidal-comparisons]; the formula becomes the coefficient naturality proved in
Steps 4 and 7. In degree $p=q=0$, Step 8 gives exactly the ordinary tensor of global sections
followed by the specified pairing. If a factor is zero or the scheme is empty, both sides
vanish, since the corresponding section complexes are zero. Disconnected schemes remain included
because Step 1 uses the ring $\mathbf Z$ on the point throughout.
-/
theorem ordinaryEtaleCup_functoriality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' G' H' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : ordinaryEtaleTensor X F G ⟶ H) (e' : ordinaryEtaleTensor Y F' G' ⟶ H')
    (a : (upperStar AddCommGrpCat.{u + 1} f).obj F ⟶ F')
    (b : (upperStar AddCommGrpCat.{u + 1} f).obj G ⟶ G')
    (c : (upperStar AddCommGrpCat.{u + 1} f).obj H ⟶ H')
    (he : (upperStar AddCommGrpCat.{u + 1} f).map e ≫ c =
      ordinaryEtaleTensorPullback f F G ≫ ordinaryEtaleTensorMap Y a b ≫ e')
    (p q : ℕ) (x : Sheaf.H F p) (y : Sheaf.H G q) :
    Sheaf.H.map c (p + q) (cohomologyMap f H (p + q) (ordinaryEtaleCup X e p q x y)) =
      ordinaryEtaleCup Y e' p q
        (Sheaf.H.map a p (cohomologyMap f F p x))
        (Sheaf.H.map b q (cohomologyMap f G q y)) := by
  sorry

end AlgebraicGeometry.Etale
end
