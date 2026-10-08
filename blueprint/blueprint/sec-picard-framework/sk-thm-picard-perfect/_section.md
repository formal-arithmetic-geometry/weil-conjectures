+++
id = "sk-thm-picard-perfect"
kind = "section"
title = "Openness of the perfect locus"
order = 677
uses = ["sk-def-av-jacobian", "sk-def-av-pic"]
lean = ["AlgebraicGeometry.Scheme.Modules.isOpen_setOf_hFiber_le", "AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_restrict", "AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_higherDirectImage_restrict"]
+++
*Theorem (sketch).*

With $f$ and $\cF$ as above, fix $i\in\Z$ and $r\ge0$ and write
$h^q(t):=\dim_{\kappa(t)}H^q(X_t,\cF_t)$. The locus

$$
U_{i,\le r}:=\{t\in T:\ h^q(t)=0\ \text{for all }q\neq i\ \text{and}\ h^i(t)\le r\}
$$

is *open* in $T$, and over it $Rf_*\cF$ is, Zariski locally on
$U_{i,\le r}$, isomorphic to a finite free module placed in degree $i$,
of rank $h^i(t)$, its formation commuting with every base change
$T'\to U_{i,\le r}$. Consequently $h^i$ is locally constant on
$U_{i,\le r}$, the locus

$$
U_{i,r}:=\{t\in T:\ h^q(t)=0\ \text{for all }q\neq i\ \text{and}\ h^i(t)=r\}
$$

is open as well, and on $U_{i,r}$ one has $R^qf_*\cF=0$ for $q\neq i$,
$R^if_*\cF$ finite locally free of rank $r$, and the base-change maps of
[sk-thm-picard-semicon] are isomorphisms; a morphism $T'\to T$
factors through $U_{i,r}$ if and only if $Rf_{T',*}\cF_{T'}$ is
isomorphic to a finite locally free $\cO_{T'}$-module of rank $r$
placed in degree $i$. No reducedness of $T$ is needed.

## Proof

Upper semicontinuity ([sk-thm-picard-semicon]) makes each condition
$h^q(t)=0$ ($q\neq i$) and $h^i(t)\le r$ open, and locally only finitely
many $q$ matter (the complex $K^\bullet$ below is bounded), so
$U_{i,\le r}$ is open. Over an affine open of $U_{i,\le r}$ let
$K^\bullet=[K^a\to\dots\to K^b]$ be the bounded complex of finite free
modules of the proof of [sk-thm-picard-semicon], whose formation
commutes with base change, so that
$H^q(K^\bullet\otimes\kappa(t))=H^q(X_t,\cF_t)$. At $t\in U_{i,\le r}$
the complex $K^\bullet\otimes\kappa(t)$ is exact outside degree $i$.
If $b>i$, then $d^{b-1}\otimes\kappa(t)$ is surjective, so by Nakayama
$d^{b-1}$ is surjective near $t$ and, its target being free, split:
$K^\bullet$ is locally quasi-isomorphic to the shorter complex
$[K^a\to\dots\to\ker d^{b-1}]$ of finite free modules. If $a<i$, then
$d^a\otimes\kappa(t)$ is injective, so some maximal minor of $d^a$ is a
unit near $t$, $d^a$ is a split injection there, and $K^\bullet$ is
locally quasi-isomorphic to $[\operatorname{coker}d^a\to\dots\to K^b]$.
After finitely many such steps $K^\bullet$ is, near $t$, quasi-isomorphic
to a single finite free module $M$ placed in degree $i$, and these
reductions commute with base change. Hence $h^i(t')=\operatorname{rk}M$
for all $t'$ near $t$, which gives the local constancy of $h^i$ on
$U_{i,\le r}$ (so $U_{i,r}$ is open and closed in $U_{i,\le r}$), the
local description $R^if_*\cF=M$, the vanishing of $R^qf_*\cF$ for
$q\neq i$, and the base-change isomorphisms. For the functorial
characterization: if $Rf_{T',*}\cF_{T'}\cong\mathcal E[-i]$ with $\mathcal E$ locally
free of rank $r$, then every $t'\in T'$ has $h^q(t')=r\,\delta_{q,i}$,
and $h^q(t')=h^q(t)$ for $t$ the image of $t'$ (cohomology commutes with
field extension), so $T'\to T$ factors through the open $U_{i,r}$; the
converse is base change. The detailed forms are Blueprint 50,
`lem-pc-perfect-locus` and `lem-pc-flat-rf-open`.
