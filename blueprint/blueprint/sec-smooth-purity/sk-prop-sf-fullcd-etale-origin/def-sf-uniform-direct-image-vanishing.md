+++
id = "def-sf-uniform-direct-image-vanishing"
kind = "definition"
title = "Uniform vanishing of the higher direct images"
order = 1788
uses = ["def-weil-finite-torsion-constructibility", "def-weil-pbc-constructible-direct-image-finiteness", "def-weil-pbc-direct-image", "def-weil-pbc-etale-site", "def-weil-scheme-morphism-properties"]
+++
Fix the global finite-field datum, a prime $\ell\ne p$, an integer
$n\geq1$, and put $A=A_{E,n}$, a finite local ring; every sheaf of
$A$-modules is then a torsion sheaf of abelian groups. Let
$k=\overline{\mathbf F}_q$, let $X,Y$ be finite-type $k$-schemes and
let $f:X\to Y$ be a
separated finite-type
morphism. For $N\in\mathbf Z_{\geq0}$, write
$\operatorname{UDV}(f,A;N)$ if

$$
R^qf_*M=0\qquad(q>N)
$$

for the higher direct images of
$f$ on the small étale sites and for
every sheaf $M$ of $A$-modules on $X_{\Et}$. This is the vanishing
clause of the finiteness predicate $\mathrm{FIN}$ of
[def-weil-pbc-constructible-direct-image-finiteness], read on the
étale site and imposed on all module sheaves rather than on the
constructible ones only.
