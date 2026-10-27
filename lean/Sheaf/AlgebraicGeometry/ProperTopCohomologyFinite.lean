/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q79
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.OrdinaryHigherImageQuasiCoherent
import WeilConjectures.AlgebraicGeometry.HigherDirectImageOpenRestriction
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.ProperFinitePresentationClosedLimit
import Sheaf.AlgebraicGeometry.LimitFibreDimensionBound
import WeilConjectures.AlgebraicGeometry.FinitePushforwardFiniteType
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.LerayAcyclicPushforwardLinearComparison
import WeilConjectures.AlgebraicGeometry.Modules.Ext
import Sheaf.AlgebraicGeometry.ModuleDirectedColimitFinitePresentation
import WeilConjectures.AlgebraicGeometry.AffineFiniteTypeGeneratingSections
import WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.ProperNoetherianStage
import WeilConjectures.AlgebraicGeometry.FinitePresentationModuleMapDescent
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections

/-! # Finite type of the top higher direct image of a proper morphism

Source: Stacks Project, Limits, Tag 0EX4, lemma-proper-top-cohomology-finite-type
(blueprint: lem-sfb-proper-top-cohomology-finite).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a proper morphism with fibres of dimension at most `d`, the `d`-th higher
module direct image of a quasi-coherent module of finite type is quasi-coherent
and of finite type on the target. No Noetherian, flatness or finite-presentation
hypothesis is required.

Source: Stacks Project, Limits, Tag 0EX4. The source conclusion's `𝒪_X` is a typo
for `𝒪_Y` (the direct image is a module on the target).
(blueprint: lem-sfb-proper-top-cohomology-finite).

Proof (the accepted DAG split):
1. A proper morphism is quasi-compact by finite type and quasi-separated by separatedness. Hence
$R^dh_*H$ is quasi-coherent. For an affine open $V\subseteq Y$, higher direct images restrict to
those of $h_V:h^{-1}V\to V$. This morphism is proper by base change, its fibres are the original
fibres, and the restricted module remains quasi-coherent and finite type (restrict its local
generators). Since finite type is local on $Y$, it suffices to prove the claim with
$Y=\operatorname{Spec}R$. Such a $Y$ is quasi-compact and quasi-separated; so is $X$, by
permanence for quasi-compact and quasi-separated morphisms. The case of an empty target or
source is immediate, with zero output.
Uses:
- def-weil-proper-morphism
- def-weil-finite-type-morphism
- lem-pc-separated-quasi-separated
- lem-pc-ordinary-higher-image-quasi-coherent
- lem-pc-higher-direct-image-open-restriction
- lem-weil-pbc-proper-fp-permanence
- lem-weil-pbc-module-pullback-quasi-coherent
- pqf-def-coherent
- lem-weil-pbc-affine-scheme-qcqs
- lem-weil-pbc-qcqs-morphism-permanence

2. Over $Y=\operatorname{Spec}R$, affine-base cohomology identifies $\Gamma(Y,R^dh_*H)$ with
$H^d(X,H)$. This identification is $R$-linear: for $r\in R$, apply its stated naturality to
multiplication by $h^*r$ on $H$; the two induced maps are scalar multiplication by $r$. The
affine finite-type criterion therefore says that it suffices to show that $H^d(X,H)$ is a
finitely generated $R$-module. We use the same natural $R$-linear affine-base identification for
all later proper morphisms over $Y$.
Uses:
- lem-pc-cohomology-sections-affine-base
- lem-weil-pbc-quasi-coherent-finite-type-affine

3. Write $X=\varprojlim_i X_i$ over $Y$ using proper closed-immersion approximation: each
$h_i:X_i\to Y$ is proper and finitely presented, and every transition and projection $a_i:X\to
X_i$ is a closed immersion. Apply the fibre-dimension limit lemma with the constant base system
$Y$: the base transitions are identities, hence affine; the stages are finite type; and its
closed comparison maps are exactly the given transition maps. It yields an index $i$ such that
all fibres of $h_i$ have dimension at most $d$. Fix this index and write $a=a_i$, $Z=X_i$,
$g=h_i$, so $h=g\circ a$.
Uses:
- lem-weil-pbc-proper-closed-in-proper-fp
- lem-trf-limit-fibre-dimension-bound
- lem-weil-pbc-affine-scheme-qcqs

4. The closed immersion $a:X\hookrightarrow Z$ is finite: over each affine open of $Z$ it is
$\operatorname{Spec}(B/I)\to\operatorname{Spec}B$, and $B/I$ is generated by $1$ as a
$B$-module. Thus $G=a_*H$ is quasi-coherent and finite type by finite pushforward, without a
Noetherian assumption. Since $a$ is affine, $R^qa_*H=0$ for $q>0$. The module-sheaf category on
$X$ has enough injectives. Apply the base-linear acyclic Leray comparison to $a$ followed by
$g:Z\to\operatorname{Spec}R$ to obtain $H^d(Z,G)\cong H^d(X,H)$ as $R$-modules. Consequently the
finiteness problem reduces to a proper finitely presented morphism over an affine base with
fibres of dimension at most $d$ and a finite-type quasi-coherent coefficient module. Rename
these $h:X\to Y$ and $H$.
Uses:
- def-weil-closed-immersion
- def-weil-finite-integral-morphism
- lem-pc-f3-finite-pushforward-finite-type
- lem-weil-pbc-affine-morphism-cohomology-edge
- lem-pc-m1-leray-acyclic-pushforward-linear-comparison
- lem-weil-pbc-scheme-modules-enough-injectives

5. Express $H=\varinjlim_\alpha G_\alpha$ with each $G_\alpha$ finitely presented. These modules
are quasi-coherent. Choose a finite affine cover $X=\bigcup_{j=1}^m U_j$ and finitely many
sections generating $H|_{U_j}$ for each $j$. Sections on $U_j$ commute with this directed
colimit, so each chosen generator lifts to some $G_\alpha(U_j)$. Directedness gives one index
$\alpha$ above the finitely many indices. At that index $G_\alpha\to H$ contains every chosen
generator on every $U_j$ and is therefore surjective. Put $H'=G_\alpha$ and $K=\ker(H'\to H)$.
This is the finite-generator argument for the quotient used in the source; no surjectivity of
the original transition maps is needed.
Uses:
- lem-weil-pbc-module-directed-colimit-finite-presentation
- lem-weil-pbc-quasi-coherent-finite-type-affine
- lem-weil-pbc-affine-finite-type-generating-sections
- lem-weil-pbc-quasi-coherent-module-colimit-affine-sections

6. The kernel $K$ is quasi-coherent. The proper fibre-dimension vanishing theorem gives
$R^{d+1}h_*K=0$, hence $H^{d+1}(X,K)=0$ by affine-base cohomology. The long exact sequence of
right-derived global sections for $0\to K\to H'\to H\to0$ now gives a surjection
$H^d(X,H')\twoheadrightarrow H^d(X,H)$. Here the module-sheaf category has enough injectives,
and global sections is additive and left exact because it computes kernels sectionwise. The map
is $R$-linear, being induced by a module map. Images of a finite generating set generate a
quotient. It remains to prove finiteness for the finitely presented coefficient module $H'$.
Uses:
- lem-weil-pbc-quasi-coherent-module-kernel
- lem-sfb-proper-quasicoherent-fibre-dimension-vanishing
- lem-pc-cohomology-sections-affine-base
- lem-weil-pbc-derived-functor-long-exact
- lem-weil-pbc-scheme-modules-enough-injectives

7. Use the inverse system $Y_\lambda=\operatorname{Spec}R_\lambda$, indexed by the finitely
generated $\mathbf Z$-subalgebras of $R$, with limit $Y$. It is a small nonempty directed system
(adjoin the union of two finite generating sets for an upper bound). Regard it as the Noetherian
approximation of $Y$. Proper finitely presented descent gives a proper finitely presented model
$h_0:X_0\to Y_0$ with $X\cong X_0\times_{Y_0}Y$. For $\lambda\ge0$ take
$X_\lambda=X_0\times_{Y_0}Y_\lambda$. These morphisms remain proper and finitely presented. The
system has limit $X$: a compatible cone into $X_\lambda$ is precisely a map into $X_0$ and a
compatible cone into $Y_\lambda$ agreeing over $Y_0$, hence a unique map into the fibre product.
Its comparison maps are isomorphisms, hence closed immersions. The fibre-dimension limit lemma
therefore supplies a stage $j$ whose fibres all have dimension at most $d$.
Uses:
- lemma-nagata-noetherian-inverse-system-affine
- def-nagata-noetherian-inverse-system
- lem-weil-pbc-proper-noetherian-stage
- lem-weil-pbc-proper-fp-permanence
- lem-weil-pbc-qcqs-morphism-permanence
- lem-trf-limit-fibre-dimension-bound

8. Apply finite-presentation module descent to $H'$ on the cartesian system just obtained. It
gives a later index $k\ge j$ and a finitely presented quasi-coherent module $H_k$ on $X_k$ with
$H'\cong b_X^*H_k$, where $b_X:X\to X_k$ lies over $b:Y\to Y_k$. Each $Y_\lambda$ is Noetherian
because it is of finite type over $\operatorname{Spec}\mathbf Z$, and each $X_\lambda$ is
Noetherian by finite type. Thus the descent theorem's Noetherian affine-base hypotheses hold.
Finite presentation implies finite type directly from a local finite presentation, so $H_k$ is
coherent by the locally Noetherian criterion. At the earlier dimension-bounded stage $j$, proper
fibre-dimension vanishing gives vanishing above $d$ for every quasi-coherent module. Both stage
schemes are qcqs by properness over an affine scheme. Clause (a) of top-degree base change
passes this vanishing to $h_k:X_k\to Y_k$. Rename $k$ as $j$; subsequent steps use this
vanishing, without needing a new fibre-dimension assertion.
Uses:
- lem-pc-fp-module-map-descent
- lem-weil-pbc-finite-type-over-noetherian
- pqf-lem-coherent-ft-locnoeth
- lem-sfb-proper-quasicoherent-fibre-dimension-vanishing
- lem-sfb-top-degree-base-change
- lem-weil-pbc-qcqs-morphism-permanence

9. For the proper Noetherian-stage morphism $h_j:X_j\to Y_j$, coherence of higher direct images
gives $N=R^dh_{j,*}H_j$ coherent, hence quasi-coherent and finite type. Both stage schemes are
quasi-compact and quasi-separated, and vanishing above $d$ holds for every quasi-coherent
coefficient module as arranged in the preceding step. Clause (c) of top-degree base change, with
the first base change the identity and the further one $b:Y\to Y_j$, yields $b^*N\cong
R^dh_*H'$. The pullback is quasi-coherent. On affine opens its sections are a tensor extension
of those of $N$; if $n_1,\ldots,n_t$ generate the latter, $n_1\otimes1,\ldots,n_t\otimes1$
generate the extension. The affine finite-type criterion therefore shows that $b^*N$, and hence
$R^dh_*H'$, is finite type. Its sections over the affine target are finite over $R$; the
identification of step 2 gives finiteness of $H^d(X,H')$.
Uses:
- lem-pc-coherent-hi
- pqf-lem-coherent-ft-locnoeth
- lem-sfb-top-degree-base-change
- lem-weil-pbc-module-pullback-quasi-coherent
- lem-weil-pbc-module-pullback-affine-sections
- lem-weil-pbc-quasi-coherent-finite-type-affine
- lem-weil-pbc-qcqs-morphism-permanence

10. Step 6 gives finiteness for the original finite-type coefficient in the finitely presented
case. Step 4 transfers it back across the closed immersion, and step 2 turns it into finite type
of the higher direct image over every affine open of $Y$. Step 1 then glues the assertion. This
proves the stated quasi-coherence and finite type over $Y$. -/
theorem proper_top_cohomology_isQuasiCoherentFiniteType
    {X Y : Scheme.{u}} (h : X ⟶ Y) [IsProper h] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim (h.fiber y) ≤ (d : WithBot ℕ∞))
    (H : X.Modules) (hH : H.IsQuasiCoherentFiniteType) :
    Scheme.Modules.IsQuasiCoherentFiniteType
      (((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).rightDerived d).obj H) := by
  sorry

end AlgebraicGeometry
