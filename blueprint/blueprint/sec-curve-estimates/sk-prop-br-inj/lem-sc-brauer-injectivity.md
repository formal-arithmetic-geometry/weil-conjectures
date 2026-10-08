+++
id = "lem-sc-brauer-injectivity"
kind = "lemma"
title = "Brauer classes are determined by the generic fibre"
order = 902
uses = ["def-br", "lem-sc-divisor-sequence-general", "lem-sc-point-z-cohomology", "lem-sp-grothendieck-edge-maps", "thm-sc-hilbert-90"]
lean = ["AlgebraicGeometry.Scheme.injective_cohomologyMap_gmSheaf_two"]
+++
Let $X$ be an integral regular noetherian scheme (for example a
connected smooth scheme over a field) with generic point
$j:\eta=\operatorname{Spec}k(X)\to X$. Then the restriction to the
generic point induces an injection (Grothendieck)

$$
\operatorname{Br}(X):=H^2(X_{\Et},\mathbf G_m)\longrightarrow
H^2(k(X)_{\Et},\mathbf G_m)=\operatorname{Br}(k(X)).
$$

In particular this holds for every smooth connected curve $C$ over a
field, proper or not, where $H^2(C_{\Et},\mathbf G_m)$ is the Brauer
group $\operatorname{Br}(C)$ of [def-br].

## Proof

Write $X^{(1)}$ for the set of codimension-one points of $X$ and, for
$x\in X^{(1)}$, $i_x:\operatorname{Spec}k(x)\to X$ for the canonical
morphism (not a closed immersion unless $x$ is closed). The restriction
map factors as

$$
H^2(X,\mathbf G_m)\xrightarrow{\ \alpha\ }H^2(X,j_*\mathbf G_{m,\eta})
\xrightarrow{\ \beta\ }H^2(\eta,\mathbf G_m),
$$

$\alpha$ induced by the unit $\mathbf G_m\to j_*j^*\mathbf G_m=j_*\mathbf G_{m,\eta}$ and $\beta$ the edge map ([lem-sp-grothendieck-edge-maps]) of the Leray spectral sequence
$E_2^{p,q}=H^p(X,R^qj_*\mathbf G_{m,\eta})\Rightarrow H^{p+q}(\eta,\mathbf G_m)$.
We show that $\alpha$ and $\beta$ are injective.

*Step 1: the divisor sequence.* By [lem-sc-divisor-sequence-general]
the sequence of etale sheaves on $X$

$$
0\longrightarrow\mathbf G_m\longrightarrow j_*\mathbf G_{m,\eta}
\xrightarrow{\ \operatorname{div}\ }\bigoplus_{x\in X^{(1)}}i_{x*}\mathbf Z\longrightarrow0
$$

is exact, the first map being the unit used to define $\alpha$. As in
its proof, for a geometric point $\bar x\to X$ over $x\in X$ we write
$\mathcal O=\mathcal O_{X,x}$, $A=\mathcal O^{sh}_{X,\bar x}$ (a
noetherian regular local ring, hence a UFD) and
$S=\mathcal O\smallsetminus\{0\}$, so that
$A\otimes_{\mathcal O}k(X)=S^{-1}A$.

*Step 2: $\alpha$ is injective.* By the long exact cohomology
sequence of Step 1 it suffices that
$H^1(X,\bigoplus_{x}i_{x*}\mathbf Z)=0$. Since $X$ is noetherian,
hence quasi-compact and quasi-separated, etale cohomology on $X$
commutes with filtered colimits, in particular with direct sums
(*reference: Stacks Project, Etale Cohomology, cohomology commutes
with colimits on quasi-compact quasi-separated schemes*), so it
suffices that $H^1(X,i_{x*}\mathbf Z)=0$ for each $x$. The Leray
spectral sequence for $i_x$ gives the injection
$H^1(X,i_{x*}\mathbf Z)\hookrightarrow H^1(\operatorname{Spec}k(x),\mathbf Z)$
(the first edge map in the five-term exact sequence). As in the proof
of [lem-sc-point-z-cohomology], etale cohomology of
$\operatorname{Spec}k(x)$ is Galois cohomology of
$G=\operatorname{Gal}(k(x)^{sep}/k(x))$ (*reference: Stacks Project,
Etale Cohomology: etale cohomology of a field is Galois cohomology*),
so $H^1(\operatorname{Spec}k(x),\mathbf Z)=\operatorname{Hom}_{\mathrm{cont}}(G,\mathbf Z)$.
A continuous homomorphism from the profinite (compact) group $G$ to
the discrete group $\mathbf Z$ has finite image, and $\mathbf Z$ has
no nontrivial finite subgroups; so this group is $0$.

*Step 3: $\beta$ is injective.* In the Leray spectral sequence for
$j$, the edge map $E_2^{2,0}=H^2(X,j_*\mathbf G_{m,\eta})\to H^2(\eta,\mathbf G_m)$
is injective as soon as $E_2^{0,1}=H^0(X,R^1j_*\mathbf G_{m,\eta})=0$
(the only differential hitting $E^{2,0}$ is
$d_2:E_2^{0,1}\to E_2^{2,0}$). We show $R^1j_*\mathbf G_{m,\eta}=0$.
Its stalk at $\bar x$ is
$H^1((\operatorname{Spec}A\times_X\eta)_{\Et},\mathbf G_m)=H^1(\operatorname{Spec}S^{-1}A,\mathbf G_m)$
(stalks of higher direct images along a quasi-compact
quasi-separated morphism: *reference: Stacks Project, Etale
Cohomology, higher direct images and strict henselizations*), which
by Hilbert 90 ([thm-sc-hilbert-90] applied to
$Y=\operatorname{Spec}S^{-1}A$) equals
$\operatorname{Pic}(S^{-1}A)$. A localization of a noetherian UFD is
a noetherian UFD, and a noetherian UFD has trivial Picard group
(its class group vanishes and $\operatorname{Pic}$ injects into the
class group of a noetherian normal domain). Hence
$R^1j_*\mathbf G_{m,\eta}=0$ and $\beta$ is injective.

Combining Steps 2 and 3, $\beta\circ\alpha$, which is the restriction
map to the generic point, is injective. For $C$ a smooth connected
curve over a field, $C$ is integral, noetherian and regular (its
local rings are regular, being local rings of a smooth scheme), so
the special case follows. (This is part of the classical residue
sequence of Grothendieck: *reference: Grothendieck, Le groupe de
Brauer II–III (Dix Exposés); Milne, Etale Cohomology, III.2 and
IV.2; Gille–Szamuely, Central Simple Algebras and Galois
Cohomology, Ch. 6*. For curves over an algebraically closed field,
the Stacks Project form of the divisor sequence is Theorem 59.68.1,
[Tag 03RI](https://stacks.math.columbia.edu/tag/03RI).)
