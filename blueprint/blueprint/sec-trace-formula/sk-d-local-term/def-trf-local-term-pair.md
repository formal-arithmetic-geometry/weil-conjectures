+++
id = "def-trf-local-term-pair"
kind = "definition"
title = "Local terms of an opposite pair"
order = 2336
uses = ["def-trf-correspondence", "def-trf-correspondence-between-pairs", "def-trf-integration", "def-trf-local-term", "def-trf-supported-pairing", "lem-trf-trace-class-diagonal-pairing"]
+++
Fix the coefficient conventions, put $s=\Spec k$, and let
$(C,c,u)$, $(D,d,v)$ be an opposite pair between $(X,K)$ and
$(Y,L)$, with $K\in D^b_{ctf}(X,A)$ and $L\in D^b_{ctf}(Y,A)$, in the
notation of [def-trf-correspondence-between-pairs] and
[def-trf-supported-pairing]. Put $E=E(C,D)$, the fiber product of the
two supports of [def-trf-correspondence-between-pairs], and let
$\langle u,v\rangle_{\mathrm{LV}}:A_E\to\omega_E$ be the
Borel–Moore section of [def-trf-supported-pairing]. For an
open-and-closed subscheme $j_B:B\hookrightarrow E$, the *restricted
pairing* is the restricted section of [def-trf-local-term]

$$
A_B\simeq j_B^*A_E\xrightarrow{j_B^*\langle u,v\rangle_{\mathrm{LV}}}
j_B^*\omega_E\simeq\omega_B,
$$

where the last identification uses open purity and the composition
isomorphism for dualizing complexes, as in [def-trf-local-term]. It
is defined for every open-and-closed $B$, proper or not. If $B$ is
proper over $s$, the *local term* of the pair on $B$ is

$$
\operatorname{LT}_B(u,v):=
\operatorname{LT}_B\bigl(\langle u,v\rangle_{\mathrm{LV}}\bigr)
=\int_B j_B^*\langle u,v\rangle_{\mathrm{LV}}\in A,
$$

the integral of [def-trf-integration]; the ambient $E$ need not be
proper. For an endocorrespondence $(C,c,u)$ of $(X,K)$ ([def-trf-correspondence]),
i.e. $(Y,L)=(X,K)$, paired with the diagonal $(X,\Delta,1_K)$, so that $E=\operatorname{Fix}(c)$ and
$\langle u,1_K\rangle_{\mathrm{LV}}=\operatorname{Tr}_c(u)$ by
[lem-trf-trace-class-diagonal-pairing], this gives, for
open-and-closed $B\subseteq\operatorname{Fix}(c)$ proper over $s$,

$$
\operatorname{LT}_B(u):=\operatorname{LT}_B(u,1_K)
=\int_B j_B^*\operatorname{Tr}_c(u),
$$

which is the local term $\operatorname{LT}_B(u)$ of
[def-trf-local-term]. At a Frobenius fixed point $\bar x$,
$\operatorname{LT}_{\bar x}$ means the local term on the reduced
open-and-closed point component $B_{\bar x}\simeq\Spec k$ of
$\bar x$, as in [def-trf-local-term].
