+++
id = "thm-trf-verdier-duality"
kind = "theorem"
title = "External duality for the fixed-point trace"
order = 2316
uses = ["def-trf-admissibility", "def-trf-coefficient-conventions", "def-trf-correspondence", "def-trf-dualizing-complex", "def-trf-external-product", "def-trf-trace-class-source", "def-weil-exceptional-inverse-image", "def-weil-finite-tor-amplitude", "lem-trf-exceptional-internal-hom-exchange", "thm-trf-kunneth-verdier"]
+++
Use the finite coefficient ring
$A=A_{E,n}$, an admissible
correspondence
$c=(c_1,c_2):C\to X\times_sX$, and
$K\in D^b_{ctf}(X,A)$ in the
finite-Tor constructible category.
Assume also that the total map $c$ and the two projections from
$X\times_sX$ are exceptionally admissible. There is a natural
external-duality isomorphism

$$
R\mathcal Hom_A(p_2^*K,p_1^!K)
\simeq K\boxtimes_A^L D_XK,
$$

where $p_i$ are the projections,
$D_XK=R\mathcal Hom_A(K,\omega_{X,A})$ is the
Verdier dual, and the
external product has this order.
It is compatible with evaluation and with the exceptional
tensor–Hom adjunction, and it yields the comparison

$$
\mathcal H_c(K)\simeq Rc^!(K\boxtimes_A^L D_XK),
$$

where $\mathcal H_c(K)$ is the
trace-class source and
$Rc^!$ is the exceptional
inverse image.

## Proof

Step 1 (the first comparison). Apply the Kunneth–Verdier isomorphism
[thm-trf-kunneth-verdier] of the trace-formula chapter to the case
$X=Y$, $M=N=K$. With the projections $p_1,p_2:X\times_sX\to X$,
its source $M\boxtimes_A^{\mathrm L}D_YN$ becomes
$K\boxtimes_A^{\mathrm L}D_XK$ and its target
$\RHom_A(p_Y^*N,p_X^!M)$ becomes
$\RHom_A(p_2^*K,p_1^!K)$, so

$$
\kappa_{K,K}:K\boxtimes_A^{\mathrm L}D_XK
\xrightarrow{\ \sim\ }
\RHom_A(p_2^*K,p_1^!K)
$$

is the first display, read in the inverse direction.

Step 2 (the second comparison). By [def-trf-trace-class-source],

$$
\mathcal H_c(K)=R\mathcal Hom_A\bigl(Lc_2^*K,Rc_1^!K\bigr) .
$$

Since $Lc_2^*=c^*p_2^*$ and $Rc_1^!=(p_1c)^!=c^!p_1^!$ by the
composition identities of the six-operation package, the exceptional
internal-Hom exchange [lem-trf-exceptional-internal-hom-exchange],
applied to the admissible $c$ with $M=p_2^*K$ and $N=p_1^!K$, gives

$$
R\mathcal Hom_A\bigl(c^*p_2^*K,c^!p_1^!K\bigr)
\cong
c^!R\mathcal Hom_A(p_2^*K,p_1^!K).
$$

Composing with the inverse of Step 1 under $c^!$ yields the second
display.

Step 3 (compatibilities). The isomorphism of Step 1 is $\kappa_{K,K}$,
which by its construction in [thm-trf-kunneth-verdier] is the
adjoint-canonical comparison, hence compatible with evaluation and with
the tensor–Hom adjunction; the exchange of Step 2 is likewise
adjoint-canonical by [def-trf-admissibility]. Both compatibilities
therefore hold.
