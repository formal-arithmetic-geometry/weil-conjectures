+++
id = "prop-sf-open-closed-triangle-all-stages"
kind = "theorem"
title = "The open–closed triangle at every coefficient stage"
order = 1851
tags = ["latex:proposition"]
uses = ["def-weil-algebraically-closed-coefficients", "def-weil-derived-complete", "def-weil-derived-complete-integral-detailed", "def-weil-derived-direct-image", "def-weil-derived-pullback-tensor-hom", "def-weil-frobenius-detailed", "def-weil-integral-rational-qbar-compact-support", "def-weil-open-closed-recollement", "def-weil-rationalization-karoubi", "def-weil-weil-sheaf-complex", "fix-lem-exchanges", "lem-cbc-completed-extension-zero-comparison", "lem-cbc-open-closed-recollement", "lem-cbc-proetale-extension-zero-comparison", "lem-sf-proetale-constructible-origin", "lem-weil-pbc-comparison-pullback", "lemma-weil-pbc-completed-pullback-reduction", "prop-weil-open-closed-recollement-adjunctions", "prop-weil-pbc-comparison-direct-image", "prop-weil-pbc-descent-functors", "prop-weil-pbc-direct-image-limits", "prop-weil-pbc-rational-transport", "prop-weil-pbc-roos-triangle", "prop-weil-pbc-scalar-extension", "prop-weil-pbc-site-comparison-finite-level", "thm-weil-pbc-verdier-axioms"]
+++
Let $X$ be a separated finite-type $k$-scheme, let $i:Z\hookrightarrow X$ be
a closed immersion and $j:U\hookrightarrow X$ the complementary open
immersion. Let $\Lambda$ be one of the coefficient stages
$A_{E,n},\mathcal O_E,E,\Qlb$, with the categories $D^b_c(-,\Lambda)$
([def-weil-derived-complete-integral-detailed],
[def-weil-rationalization-karoubi],
[def-weil-algebraically-closed-coefficients]), the pullbacks $i^*,j^*$ of
[def-weil-derived-pullback-tensor-hom], the direct image $i_*=Ri_*$ of
[def-weil-derived-direct-image] and the extension by zero $j_!=Rj_!$ of
[def-weil-integral-rational-qbar-compact-support]. For
$K\in D^b_c(X,\Lambda)$ the open counit and the closed unit extend to a
distinguished triangle, the open–closed recollement triangle of
[def-weil-open-closed-recollement],
$$
j_!j^*K\longrightarrow K\longrightarrow i_*i^*K
\longrightarrow j_!j^*K[1].
$$
Moreover $\operatorname{Hom}(j_!j^*K[m],i_*i^*K)=0$ for all $m$; hence the
third arrow is uniquely determined by the other two and the triangle is
functorial in $K$. If $X=X_0\otimes_{k_0}k$, $Z$, $U$ come from
$k_0$-schemes, $\Lambda\in\{E,\Qlb\}$ and $K$ is a Weil complex
([def-weil-weil-sheaf-complex]), then all three arrows are
Weil-equivariant.

## Proof

*Finite stage.* Let $A=A_{E,n}$. By [lem-sf-proetale-constructible-origin]
write $K\cong\nu_X^*G$ with $G$ a bounded constructible complex on the étale
site. The étale triangle $j_!j^{-1}G\to G\to i_*i^{-1}G\to$ is
[lem-cbc-open-closed-recollement]. Apply the exact functor $\nu_X^*$
([prop-weil-pbc-site-comparison-finite-level]). The comparisons of
[lem-cbc-proetale-extension-zero-comparison] (for $j_!$),
[lem-weil-pbc-comparison-pullback] (for $j^*,i^*$) and
[prop-weil-pbc-comparison-direct-image] (for the finite, hence
quasi-compact, $i$) identify its vertices with $j_!j^*K$, $K$, $i_*i^*K$.
These comparisons are those of the adjunctions of
[prop-weil-open-closed-recollement-adjunctions], so the first two arrows
become the pro-étale open counit and closed unit. Hom vanishing: by
[prop-weil-open-closed-recollement-adjunctions] $j_!\dashv j^*$, and
$j^*i_*=0$ (the closed fibre of an object over $U$ is empty), so
$\operatorname{Hom}(j_!N[m],i_*M)=\operatorname{Hom}(N[m],j^*i_*M)=0$. Two
completions of the first two arrows differ by an automorphism $h$ of the third
vertex with $h-\operatorname{id}$ factoring through $i_*i^*K\to
j_!j^*K[1]$, hence through a zero map; so $h=\operatorname{id}$.

*Integral stage.* Put $R=\mathcal O_E$, $A_n=R/\varpi_E^n$,
$K_n=K\otimes^L_RA_n$. The operations have the finite reductions:
$(j^*K)_n\cong j^*K_n$ and $(i^*K)_n\cong i^*K_n$ by
[lemma-weil-pbc-completed-pullback-reduction];
$(i_*M)_n\cong i_*M_n$, with $i_*M$ derived complete, by
[prop-weil-pbc-direct-image-limits]; and for the extension by zero,
[lem-cbc-completed-extension-zero-comparison] applied to the identity square
shows that $j_!N$ is derived complete with $(j_!N)_n\cong j_!N_n$, so it is
the derived limit $R\varprojlim_n\operatorname{Res}_nj_!N_n$ of
[def-weil-integral-rational-qbar-compact-support]. Define the counit
$j_!j^*K\to K$ and the unit $K\to i_*i^*K$ as the derived limits of the
finite counits and units, using $K\cong R\varprojlim_n\operatorname{Res}_nK_n$;
their reductions are the finite maps.

Hom vanishing. If $P$ is integral and
$M=R\varprojlim_n\operatorname{Res}_nM_n$, then
$\operatorname{Hom}(P[m],\operatorname{Res}_nM_n)=
\operatorname{Hom}_{A_n}(P_n[m],M_n)$ by extension and restriction of
scalars; if these vanish for all $m,n$, the Roos triangle of
[prop-weil-pbc-roos-triangle] gives $\operatorname{Hom}(P[m],M)=0$. With
$P=j_!j^*K$, $M=i_*i^*K$ the finite vanishing gives the integral one.

Completion criterion. Let $u:A\to B$, $v:B\to C$ be maps of derived complete
objects with $A,B\in D^b_c(X,R)$, $\operatorname{Hom}(A[m],C)=0$ for all
$m$, and reductions $A_n\to B_n\to C_n$ extending to distinguished
triangles. Then $vu=0$, because $\operatorname{Hom}(A,C)=0$. Choose a
cone $B\xrightarrow{w}C'\to A[1]$ of $u$; then $v=\varphi w$ for a unique
$\varphi:C'\to C$. Modulo $\varpi_E^n$, TR3 and the finite uniqueness make
$\varphi_n$ an isomorphism, so the cone of $\varphi$ is derived complete with
zero reductions, hence zero by [def-weil-derived-complete]. Thus
$A\to B\to C\to A[1]$ is distinguished. Applied to the counit and unit this
gives the integral triangle, and $i_*i^*K\in D^b_c(X,R)$.

*Rational stage.* By [def-weil-rationalization-karoubi] the objects of
$D^b_c(-,E)$ are the integral ones, and by
[prop-weil-pbc-rational-transport] the exact $R$-linear functors
$i^*,j^*,i_*,j_!$ and the two maps are the rationalized integral ones. The
image of a distinguished integral triangle is distinguished, and Hom groups
become $\operatorname{Hom}\otimes_RE=0$.

*Algebraically closed stage.* An object of $D^b_c(-,\Qlb)$ is a pair
$(E,K)$ ([def-weil-algebraically-closed-coefficients]). The operations are
the descended functors of [prop-weil-pbc-descent-functors], built from the
scalar-extension compatibilities of [prop-weil-pbc-scalar-extension] (for
$j_!$, the finite-stage compact-support functor of
[def-weil-integral-rational-qbar-compact-support]); the two maps descend as
compatible transformations. The finite-stage inclusions are exact by
[thm-weil-pbc-verdier-axioms], so the $E$-stage triangle gives the
$\Qlb$-triangle, and Hom groups are filtered colimits of vanishing
$E$-stage groups.

*Weil structures.* The geometric Frobenius $g_X$ of
[def-weil-frobenius-detailed] restricts to $g_U$ and $g_Z$, and the squares
formed by $j$, $i$ and these automorphisms are cartesian. The exchange maps
of [fix-lem-exchanges] for these automorphism squares are isomorphisms
(their inverses come from the inverse squares), and they give the Weil
structures on $j_!$ and $i_*$; the pullbacks use $g_U^*j^*=j^*g_X^*$ and
$g_Z^*i^*=i^*g_X^*$. The counit and unit are equivariant, since the exchange
maps are built from, and paste with, the same units and counits
([fix-lem-exchanges]). Transporting the triangle along $g_X^*$ and the Weil
isomorphisms gives a distinguished triangle with the same first two arrows;
by the uniqueness above it has the same third arrow, which is therefore
equivariant.
