+++
id = "lem-sc-flat-base-change-coherent"
kind = "lemma"
title = "Flat base change for coherent cohomology"
order = 715
uses = ["lem-sc-cech-spectral"]
+++
Let $X$ be a proper scheme over a field $k$, $k\to k'$ a flat
$k$-algebra (e.g. a field extension) and $\mathcal F$ a
quasi-coherent sheaf on $X$. Then for all $i\geq0$

$$
H^i(X_{k'},\mathcal F_{k'})\cong H^i(X,\mathcal F)\otimes_kk'.
$$

In particular, if $k'\supseteq k$ is an extension of algebraically
closed fields and $\mathcal F=\mathcal O_X$, then

$$
\dim_{k'}H^i(X_{k'},\mathcal O_{X_{k'}})=\dim_kH^i(X,\mathcal O_X).
$$

## Proof

Since $X$ is proper over $k$, it is quasi-compact and
quasi-separated, hence covered by finitely many affine open subsets
$U_1,\dots,U_r$, and their base changes $U_{j,k'}$ cover
$X_{k'}$. For a quasi-coherent sheaf $\mathcal F$, the cohomology
$H^\bullet(X,\mathcal F)$ is computed by the Cech complex of the
affine covering $\{U_j\to X\}$: in the Cech-to-cohomology spectral
sequence of the covering ([lem-sc-cech-spectral], applied to
the Zariski site),

$$
E_2^{pq}=\check H^p(\mathfrak U,\underline H^q(\mathcal F)),
$$

and $\underline H^q(\mathcal F)(U_J)=H^q_{\Zar}(U_J,\mathcal F)=0$
for $q>0$, because each intersection
$U_J=U_{j_0}\cap\dots\cap U_{j_q}$ is affine (higher Zariski
cohomology of a quasi-coherent sheaf on an affine scheme vanishes);
so the spectral sequence degenerates and
$H^i(X,\mathcal F)=\check H^i(\mathfrak U,\mathcal F)$. For every multi-index $J=\{j_0<\dots<j_q\}$, the
intersection $U_J:=U_{j_0}\cap\dots\cap U_{j_q}$ is affine and
$U_{J,k'}:=U_J\times_kk'$ is affine, with

$$
\Gamma(U_{J,k'},\mathcal F_{k'})
=\Gamma(U_J,\mathcal F)\otimes_kk',
$$

by flatness of $k\to k'$ (for $U_J=\operatorname{Spec}A$ and
$\mathcal F|_U=\widetilde M$, the tensor product $M\otimes_kk'$
is a module over $A\otimes_kk'$). Because $(-)\otimes_kk'$ is
exact (flatness), the Cech complex computing
$H^\bullet(X_{k'},\mathcal F_{k'})$ is obtained from the Cech
complex computing $H^\bullet(X,\mathcal F)$ by applying
$(-)\otimes_kk'$, and therefore

$$
H^i(X_{k'},\mathcal F_{k'})\cong H^i(X,\mathcal F)\otimes_kk'.
$$

The dimension statement follows: a $k$-basis of
$H^i(X,\mathcal F)$ remains a $k'$-basis after extension of
scalars, because the field extension $k\to k'$ is flat (injective).
