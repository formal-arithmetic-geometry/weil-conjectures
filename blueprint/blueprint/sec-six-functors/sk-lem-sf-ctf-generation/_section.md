+++
id = "sk-lem-sf-ctf-generation"
kind = "section"
title = "Finite/open generation of $\\Dctf$"
order = 2219
uses = ["sk-lem-sf-determination", "sk-lem-sf-flat-model", "sk-prop-sf-open-closed-triangle", "sk-thm-sf-ctf-stability"]
lean = ["AlgebraicGeometry.Etale.ctf_generated_by_rightDerivedLowerStar_rightDerivedLowerShriek"]
+++
*Lemma (sketch).*

On a separated finite-type $k$-scheme $X$, $\Dctf(X,\Lambda)$ is generated as
a thick subcategory by the objects $Rg_*j_!L$, where $U\subset X$ is a locally
closed stratum of a stratification, $j:U\hookrightarrow\overline U$ is the
open immersion into its closure, $g:\overline U\hookrightarrow X$ is the closed
immersion of the closure, and $L$ is a lisse sheaf of $\Lambda$-modules on $U$
with flat stalks. The lisse coefficients cannot in general be replaced by
constant ones $L=\Lambda_U$.

## Proof

The generators lie in $\Dctf$: a lisse flat $L$ has Tor amplitude $[0,0]$,
and $j_!$, $Rg_*$ preserve $\Dctf$ ([sk-thm-sf-ctf-stability]).
Conversely, when $\Lambda$ is not a field the truncations of an object of
$\Dctf$ need not have finite Tor amplitude, so one dévisses a flat model
rather than the cohomology sheaves. By the constructible variant of
[sk-lem-sf-flat-model] (whose input is that every constructible sheaf is a
quotient of a finite sum of the flat constructible sheaves $j_{V!}\Lambda_V$,
$V\to X$ affine étale, Stacks 095M, and that kernels and cokernels of
maps of constructible sheaves are constructible), $K\in\Dctf$ is isomorphic
to a bounded complex $P$ of flat constructible sheaves. The
stupid-truncation triangles
$\sigma_{\ge q+1}P\to\sigma_{\ge q}P\to P^q[-q]\xrightarrow{+1}$ reduce the
claim to one flat constructible sheaf $F$. Choose a dense open
$U\subset X$ on which $F$ is lisse, with closed complement $i:Z\hookrightarrow
X$. The sequence $0\to j_!(F|_U)\to F\to i_*i^*F\to0$ of
[sk-prop-sf-open-closed-triangle] has $F|_U$ lisse with flat stalks and
$i^*F$ flat constructible on $Z$, of smaller dimension; induction on
dimension, pushing forward along the closed immersion $i$, exhibits $F$ as a
finite iterated extension of objects $Rg_*j_!L$ of the stated form, and each
extension is a distinguished triangle. Hence, by [sk-lem-sf-determination],
a natural transformation of exact functors on $\Dctf$ is invertible as soon
as it is invertible on these generators. For a single generator one may
further pass to a finite étale Galois cover $\pi:V\to U$ trivializing $L$,
on which $\pi^*L$ is constant; this reduction is local on $U$ and is not a
dévissage, since $L$ need not be a direct summand of $\pi_*\pi^*L$ when
$\ell$ divides the order of the monodromy. Constant coefficients alone do not
generate: for $X=\mathbf G_m$, $p\ne2$, $\Lambda=\mathbf F_3$, the complexes
whose generic-stalk cohomology has only trivial $\pi_1$-composition factors
form a thick subcategory containing every $Rg_*j_!\Lambda_U$ but not the
order-$2$ Kummer sheaf.

Uses: `\Cref{sk-lem-sf-determination}`, `\Cref{sk-prop-sf-open-closed-triangle}`, `\Cref{thm-sf-ctf-stability}`, `\Cref{lem-sf-flat-model}`
