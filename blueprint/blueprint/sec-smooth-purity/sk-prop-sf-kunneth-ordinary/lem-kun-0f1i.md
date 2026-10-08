+++
id = "lem-kun-0f1i"
kind = "lemma"
title = "Base change towards spectra of fields"
order = 1777
uses = ["def-kun-bc-property", "def-kun-separably-closed", "def-kun-torsion-invertible", "def-kun-unbounded-exchange", "def-weil-pbc-hypercohomology-filtrations", "def-weil-pbc-scheme-conventions", "lem-kun-0eys", "lem-kun-0f1c", "lem-kun-0f1d", "lem-kun-0f1i-normal", "lem-kun-bc-base-change", "lem-kun-bc-map-on-cohomology", "lem-kun-geometric-reduced-perfect", "lem-kun-invertible-orders-colimit", "lem-kun-sep-closure-conservative", "lem-kun-stalk-faithful-derived", "lem-kun-unbounded-exchange-agrees", "lem-kun-zn-sheaf-invertible-orders", "lemma-weil-pbc-direct-image-filtered-colimit", "thm-weil-pbc-universal-homeomorphism-invariance"]
+++
Let $K$ be a field and let $X$ be a scheme of finite type over
$K$. For any commutative diagram

$$
\begin{array}{ccccc}
X&\longleftarrow&X'&\longleftarrow&Y\\
\Big\downarrow{\scriptstyle f}&&\Big\downarrow{\scriptstyle f'}&&\Big\downarrow{\scriptstyle h}\\
\Spec(K)&\longleftarrow&S'&\longleftarrow&T
\end{array}
$$

of schemes over $K$ with $X'=X\times_{\Spec(K)}S'$ and
$Y=X'\times_{S'}T$ and with $g:T\to S'$ quasi-compact and quasi-separated, and for every abelian sheaf $F$ on $T_{\Et}$ whose
stalks are torsion of orders invertible in $K$, the exchange
morphism

$$
(f')^{-1}Rg_*F\longrightarrow Rh_*e^{-1}F
$$

is an isomorphism. (*Source:* Stacks Project, Tag
[0F1I](https://stacks.math.columbia.edu/tag/0F1I), in the case
used in this chapter, namely with $X$ of finite type over $K$; the
general case of that tag reduces to this one by the approximation of a
quasi-compact quasi-separated scheme by finite type models, which is not
needed here.)

## Proof

*Reduction to affine $X$.* The question is local on $X$
([lem-kun-stalk-faithful-derived] and
[lem-kun-bc-base-change]), hence we may assume $X$ is affine.

*Reduction to $\kunZn$-coefficients.* Similarly, we may
write $F=\varinjlim_{n\in I_K}F[n]$
([def-kun-torsion-invertible] and
[lem-kun-invertible-orders-colimit]); since both sides of the exchange
morphism commute with filtered colimits in $F$
([lemma-weil-pbc-direct-image-filtered-colimit] for the
quasi-compact quasi-separated $g,h$, and exactness of the
inverse images), the same argument reduces us to the case where
$F$ is a sheaf of $\kunZn$-modules for some $n$ invertible in
$K$, which has orders invertible in $K$ by
[lem-kun-zn-sheaf-invertible-orders].

*Passage to the algebraic closure.* We may replace $K$ by
its algebraic closure $\bar K$: formation of the direct image
commutes with base change to $\bar K$ by [lem-kun-0f1c]
(this works for both $g$ and $h$), the exchange morphism is
compatible with this base change
([lem-kun-bc-base-change]), and it suffices to prove the
agreement after restriction to $X'_{\bar K}$ by
[lem-kun-sep-closure-conservative].

*Reduction of $X$.* Next, we may replace $X$ by its
reduction, because étale cohomology is invariant under universal
homeomorphisms ([thm-weil-pbc-universal-homeomorphism-invariance]).
After this replacement the morphism $X\to\Spec(K)$ is flat, of
finite presentation, with geometrically reduced fibres, and the same
holds for any base change, in particular for $X'\to S'$
([lem-kun-geometric-reduced-perfect], where $K$ is
algebraically closed hence perfect). Hence
$f^{-1}g_*F\to h_*e^{-1}F$ is an isomorphism by
[lem-kun-0eys]; in the notation of
[def-kun-bc-property] this is $BC(f',n,0)$, the identification
of the sheaf-level map with the zeroth cohomology sheaf of the derived
exchange morphism being [lem-kun-unbounded-exchange-agrees].

*Conclusion by contraposition.* Suppose for contradiction
that the derived exchange morphism is not an isomorphism for some
$F$ as above. By the spectral sequences of
[def-weil-pbc-hypercohomology-filtrations] (and
[lem-kun-bc-base-change] together with
[lem-kun-bc-map-on-cohomology], which identify the induced maps on
$\mathcal H^q$ with the maps of
[def-kun-bc-property]), there is a minimal $q\ge1$ such that
$BC(f',n,q)$ fails while $BC(f',n,q-1)$ holds. At this point we
may apply [lem-kun-0f1d] to see that it suffices to prove:
given a commutative diagram

$$
\begin{array}{ccccc}
X&\longleftarrow&X'&\longleftarrow&Y\\
\Big\downarrow{\scriptstyle f}&&\Big\downarrow{}&&\Big\downarrow{\scriptstyle h}\\
\Spec(K)&\longleftarrow&S'&\longleftarrow&\Spec(L)
\end{array}
$$

with both squares cartesian, where $S'$ is affine, integral, and
normal with algebraically closed function field $L$, then
$R^qh_*\underline{\mathbf Z/d\mathbf Z}=0$ for $q>0$ and
$d\mid n$. (Indeed, if some $BC(f',n,q)$ failed,
[lem-kun-0f1d] would produce such a diagram with
$R^qh_*\underline{\mathbf Z/d\mathbf Z}\ne0$; note that
$X''=X'\times_{S'}S''=X\times_KS''$ since
$X'=X\times_KS'$.) But this vanishing is exactly
[lem-kun-0f1i-normal], which is already proved. This
contradiction shows that the derived exchange morphism is an
isomorphism for every $F$, as desired.
