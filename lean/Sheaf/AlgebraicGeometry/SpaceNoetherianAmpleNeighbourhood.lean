/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.TraceFormula.SpaceLineModuleProjInput
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Sheaf.AlgebraicGeometry.EtaleOpenChartMorphismDescent
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.ProjectiveMorphismChartPreimage
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AmplePullback
import Sheaf.AlgebraicGeometry.FreeProjectiveBundleBaseChangeSpace
import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections

/-! # Ampleness near a schematic fibre over a Noetherian base

Source: Stacks Project, Divisors on Spaces, Tag 0D3A (lemma-ample-in-neighbourhood),
with relative ampleness interpreted by Tags 0D31 and 0D32
(blueprint: lem-sfb-space-noetherian-ample-neighbourhood).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An ample schematic fibre of a proper algebraic space over a Noetherian scheme
has a schematic relatively ample neighbourhood.

The sheaf pullback squares state schematicity without selecting a scheme structure
in advance. `lineTestFamily` is the existing canonical tensor-pullback family of the
specified small-etale line module. Its module on a test is determined by descent,
with its identification with that line module retained. Thus the fibre hypothesis
and the conclusion use ordinary invertible modules on their representing schemes.
The conclusion tests every affine open of the neighbourhood, as in Tag 0D32.

Source: Stacks Project, Divisors on Spaces, Tag 0D3A (lemma-ample-in-neighbourhood)
(blueprint: lem-sfb-space-noetherian-ample-neighbourhood).

Proof, following the nine steps of the node:

1. Use [lem-trf-space-enlarged-etale-ringed-site-model] for the tensor pullbacks. Pulling back a
trivialization of a line and its inverse shows that its pullback and its tensor powers remain
lines; multiplying elementary tensors identifies pullback of a tensor power with the power of the
pullback. On schemes [lem-trf-scheme-zariski-etale-quasi-coherent-equivalence] identifies these
lines, their sections and their pullbacks with the ordinary invertible modules. If $X_t$ is empty,
properness makes $f(|X|)$ closed, and $t$ is outside it. Choose an affine neighbourhood $V$ in its
complement by [lem-weil-pbc-affine-opens-basis]. Then $X_V$ is the empty scheme, and ampleness on
every affine inverse image is vacuous by [def-weil-pbc-ample-invertible-module]. Hence assume
$X_t$ nonempty.

2. Apply [lem-sfb-space-ample-fibre-section-lifting] to obtain a bound $a$. The scheme $X_t$ is
proper over $\kappa(t)$ by [lem-sfb-space-proper-base-change], hence locally of finite type. Apply
[lem-trf-affine-eventual-power-immersion] to its ample line $L_t$. Choose $d\geq\max(a,1)$ large
enough to obtain an immersion $j:X_t\to\mathbf P^r_{\kappa(t)}$ and $j^*\mathcal O(1)\cong
L_t^{\otimes d}$. Projective space is separated by [lem-trf-projective-bundle-quotient-geometry].
Thus $j$ is proper by [lem-weil-pbc-proper-over-separated] and a closed immersion by [lem-weil-
pbc-proper-immersion-closed]. The canonical isomorphism $\theta$ of [lem-trf-free-projective-
bundle-base-change-space] between this relative-Proj projective space and $\mathbf
P(\{0,\ldots,r\};\kappa(t))$ lies over the base and is, on the affine chart, the Proj comparison
fixing every $T_i$; it therefore matches the standard opens $D_+(T_i)$, the coordinates $T_l/T_i$
and the twists glued from them, so the base-change-model statements below apply. Pull back the
standard coordinates using $j^*\mathcal O(1)\cong L_t^{\otimes d}$ to get sections
$v_0,\ldots,v_r$ generating $L_t^{\otimes d}$: each coordinate trivializes on its chart and these
charts cover, by [lem-weil-pbc-projective-space-standard-charts]. Their associated morphism is $j$
by the quotient classification in [lem-trf-projective-bundle-quotient-geometry].

3. For each of the finitely many $v_i$, apply [lem-sfb-space-ample-fibre-section-lifting] at this
same $d$. Intersect their neighbourhoods and choose an affine open neighbourhood $U$ of $t$ inside
the intersection by [lem-weil-pbc-affine-opens-basis]. Restrict all lifts to get
$s_i\in\Gamma(X_U,L^{\otimes d})$ with fibre tuple $(v_i)$. Replace $T$ by $U$ and $X$ by $X_U$.
Properness persists by [lem-sfb-space-proper-base-change]. The Noetherian hypothesis was used
before this replacement; no new application of the lifting lemma is needed.

4. Put $M=L^{\otimes d}$. The locus $G$ where the $s_i$ generate $M$ is open: on a scheme etale
chart trivializing $M$, write $s_i=a_i e$; its inverse image is $\bigcup_iD(a_i)$. These opens
agree under change of trivialization and pullback; [lem-trf-etale-open-chart-morphism-descent]
gives the corresponding open subspace of $X$. The fibre lies in $G$ since the $v_i$ generate. The
complement $C=|X|\setminus|G|$ is closed, so $f(C)$ is closed and misses $t$. Replace $T$ by an
affine neighbourhood of $t$ inside $T\setminus f(C)$ and restrict $X$. Now the $s_i$ generate $M$
everywhere. Properness is preserved by [lem-sfb-space-proper-base-change].

5. Choose a surjective etale scheme atlas $p:A\to X$ as in [def-trf-algebraic-space]. On $A$,
[lem-trf-projective-bundle-quotient-geometry] applied to the quotient $\mathcal
O_A^{r+1}\twoheadrightarrow p^*M$ constructs a $T$-map $A\to P=\mathbf P^r_T$ and a quotient-
compatible twist isomorphism. Naturality of that statement makes the two maps equal on the scheme
$A\times_XA$. Apply [lem-trf-etale-open-chart-morphism-descent] with the whole atlas as its
invariant open to descend a unique $\varphi:X\to P$. The local twist isomorphisms also agree on
$A\times_XA$: each sends the same pulled-back coordinate sections to the $s_i$, and those sections
generate. They therefore give an isomorphism $\varphi^*\mathcal O_P(1)\cong M$ of module sheaves
on the small etale site. Explicitly a local section is sent by the local maps after pulling back
to the atlas, and their equality on overlaps gives its unique glued image; the inverses glue in
the same way. The same construction on any scheme test gives the quotient morphism there, by the
atlas descent's test-scheme clause. In particular the fibre map is $j$, and, once $X$ is a scheme,
the descended map is its ordinary quotient morphism. This supplies the projective-space
construction whose details the source omits.

6. The map $q:P\to T$ is proper by [lemma-nagata-projective-space-base-change-proper], transported
along the isomorphism $\theta:P\cong\mathbf P(\{0,\ldots,r\};T)$ over $T$ of [lem-trf-free-
projective-bundle-base-change-space]; hence $q$ is separated. The graph $\Gamma_\varphi:X\to
X\times_TP$ is the pullback of $\Delta_q:P\to P\times_TP$ by
$(\varphi\operatorname{pr}_X,\operatorname{pr}_P)$. It is therefore a closed immersion on every
scheme test: [lem-weil-pbc-closed-immersion-base-change] applies to that test and $\Delta_q$. By
[lem-sfb-space-closed-subspace-proper] the graph is proper. The projection $X\times_TP\to P$ is
proper by [lem-sfb-space-proper-base-change]. Their composite $\varphi$ is proper by [lem-sfb-
space-proper-composition].

7. Let $Q\subseteq|X|$ be the quasi-finite locus of $\varphi$; it is open by [lem-sfb-space-
quasifinite-locus-open]. For every point $z\in|P_t|$, the fibre of $\varphi$ over $z$ is the base
change of the closed immersion $j$ to $\operatorname{Spec}\kappa(z)$, hence is a closed subscheme
of that field spectrum by [lem-weil-pbc-closed-immersion-base-change]. It is empty or that one-
point scheme, because a field has only the zero and unit ideals. By [lem-sfb-space-finite-fibre-
quasifinite-criterion], all points of $X$ over $z$ lie in $Q$. Thus the closed set
$\varphi(|X|\setminus Q)$ misses the entire $|P_t|$. Write $W=P\setminus\varphi(|X|\setminus Q)$.
On $W$, $\varphi$ is proper by [lem-sfb-space-proper-base-change] and locally quasi-finite. The
explicit assertion in [lem-sfb-stack-separation-composition], that a proper locally quasi-finite
algebraic space over a scheme is finite over it and a scheme, applies to $\varphi^{-1}W\to W$.
Consequently this restriction is finite and its source is a scheme.

8. Since $q$ is proper, $q(P\setminus W)$ is closed; it does not contain $t$ because $P_t\subseteq
W$. Choose an affine open $V\ni t$ inside $T\setminus q(P\setminus W)$ by [lem-weil-pbc-affine-
opens-basis]. Then $P_V\subseteq W$. The preimage of this open under the finite scheme morphism
$\varphi^{-1}W\to W$ is $X_V$, and the restriction $\varphi_V:X_V\to P_V$ is finite: on an affine
open of $P_V$ it is the same finite ring map as before, using [def-weil-finite-integral-morphism].
In particular $X_V$ is a scheme. Step 5 on the scheme test $X_V\to X$ identifies $\varphi_V$ with
the morphism given by the restricted $s_i$ and identifies its hyperplane pullback with $L^{\otimes
d}|_{X_V}$.

9. Compose with the isomorphism $\theta$ over $V$ of [lem-trf-free-projective-bundle-base-change-
space], which on affine charts fixes every $T_i$ and hence matches $D_+(T_i)$ and the glued twists
$\mathcal O(1)$ with their coordinate sections. By the quotient compatibility of step 5,
$\theta\varphi_V$ pulls $\mathcal O(1)$ back to $L^{\otimes d}|_{X_V}$ with $T_i\mapsto s_i$, so
it is the morphism $\varphi_{(L^{\otimes d},(s_i))}$ of [def-weil-pbc-morphism-to-projective-
space-by-sections] by the uniqueness stated there. By [lem-weil-pbc-projective-morphism-chart-
preimage], $(X_V)_{s_i}=\varphi_V^{-1}(D_+(T_i)_V)$. The target charts are affine because $V$ is
affine, by [lem-weil-pbc-projective-space-standard-charts]. Finiteness makes their inverse images
affine by [def-weil-finite-integral-morphism]. They cover $X_V$, and each $s_i$ is a section of
the positive power $L^{\otimes d}$. Also $X_V$ is quasi-compact: its proper map to the affine,
hence quasi-compact $V$ is quasi-compact, by [lem-sfb-space-proper-base-change] and [lem-weil-pbc-
affine-scheme-qcqs]. These facts are exactly ampleness of $L_V$ in [def-weil-pbc-ample-invertible-
module]; no extraction of a root of an ample power is needed. For every affine open $B\subseteq
V$, $B\to V$ is affine by [lem-weil-pbc-morphism-affine-schemes-affine], so $X_B\to X_V$ is affine
by [lem-weil-pbc-affine-morphism-permanence]. The affine pullback theorem [lem-weil-pbc-pullback-
ample-invertible] gives ampleness of $L_B$. This is precisely the relative-ampleness conclusion.
-/
theorem exists_relativelyAmple_neighbourhood_of_noetherian
    (T : Scheme.{u}) [IsNoetherian T] (X : AlgebraicSpace T)
    (f : X ⟶ schemeSpace (Over.mk (𝟙 T))) (hf : MapIsProper f)
    (L : X.Modules) (hL : X.IsLineModule L) (t : T)
    (hfibre : ∃ (Z : Over T) (p : Z ⟶ Over.mk (T.fromSpecResidueField t))
      (q : yoneda.obj Z ⟶ X.obj.obj),
      IsPullback q (yoneda.map p) f.hom.hom
        (yoneda.map (Over.homMk (T.fromSpecResidueField t) (Category.comp_id _))) ∧
      Scheme.Modules.IsAmple Z.left
        ((lineTestFamily X L hL).module (CostructuredArrow.mk q))) :
    ∃ V : T.Opens, t ∈ V ∧
      ∃ (Z : Over T) (p : Z ⟶ Over.mk V.ι) (q : yoneda.obj Z ⟶ X.obj.obj),
        IsPullback q (yoneda.map p) f.hom.hom
          (yoneda.map (Over.homMk V.ι (Category.comp_id _))) ∧
        ∀ W : V.toScheme.Opens, IsAffineOpen W →
          @Scheme.Modules.IsAmple (p.left ⁻¹ᵁ W).toScheme
            ((Scheme.Modules.tensorPullback (p.left ⁻¹ᵁ W).ι).obj
              ((lineTestFamily X L hL).module (CostructuredArrow.mk q)))
            ((Scheme.Modules.invertible_pullback_tensor (p.left ⁻¹ᵁ W).ι).1
              ((lineTestFamily X L hL).module (CostructuredArrow.mk q))).2 := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
