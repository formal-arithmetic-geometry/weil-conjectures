+++
id = "def-trf-scheme-frobenius"
kind = "definition"
title = "Scheme and Galois Frobenius of the geometric fiber"
order = 2071
uses = ["def-weil-finite-field-fiber", "def-weil-frobenius-detailed", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties"]
+++
Fix the global finite-field datum
$p,a,q,k_0,k$, where $q=p^a$, let $X_0$ be a
finite-type
$k_0$-scheme, and put $X=X_0\times_{k_0}k$. Let
$\sigma:k\to k$, $z\mapsto z^q$, be the arithmetic Frobenius and put
$\gamma=\sigma^{-1}=\operatorname{Frob}_q$, so that
$g_\gamma=\operatorname{id}_{X_0}\times\Spec(\gamma):X\to X$ is the
geometric-Frobenius automorphism. The
$q$-power scheme Frobenius of $X_0$ is the $k_0$-morphism
$\Phi_0:X_0\to X_0$ whose affine incarnation is $a\mapsto a^q$; its
base change

$$
\Phi:=\Phi_0\times_{k_0}\operatorname{id}_k:X\longrightarrow X
$$

is a $k$-morphism with affine incarnation
$a\otimes b\mapsto a^q\otimes b$ on $A_0\otimes_{k_0}k$, and is
finite and radicial.
For $m\in\mathbf Z_{\geq0}$ write $\Phi^m$ for the $m$-fold
iterate, and write

$$
g_\sigma=\operatorname{id}_{X_0}\times\Spec(\sigma):X\longrightarrow X
$$

for the arithmetic Galois automorphism. On the
small pro-etale site, the
derived pullback functors $L\Phi^m{}^*$ and $Lg_\gamma^{m*}$ are the
pullbacks along these endomorphisms.

*Recorded in advance* from chapter *The trace formula* of the source.
