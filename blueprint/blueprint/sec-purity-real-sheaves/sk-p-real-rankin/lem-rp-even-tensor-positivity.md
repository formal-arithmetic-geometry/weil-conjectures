+++
id = "lem-rp-even-tensor-positivity"
kind = "lemma"
title = "Even tensor powers of a real sheaf are positive"
order = 2661
uses = ["def-real-weil-representation-operations", "def-weil-pbc-scheme-conventions", "def-wf-iota-real", "def-wf-weil-category", "p-linear-spectra"]
+++
Let $\mathcal G_0$ be a lisse
$\iota$-real
Weil sheaf on a
separated finite-type
$k_0$-scheme. Then for every closed point $x$ and every
$k\ge1$, with $\mathcal G_0^{\otimes k}$ the $k$-fold tensor power of
[def-real-weil-representation-operations]:

1. **(i)** the local characteristic polynomial
$\iota\det(1-tF_x,\mathcal G^{\otimes k}_{0,\bar x})$ has real
coefficients;
1. **(ii)** if $k$ is even, the power series
$$
\iota\det(1-tF_x,\mathcal G^{\otimes k}_{0,\bar x})^{-1}
=\sum_{n\ge0}a_nt^n
$$
has all coefficients $a_n\ge0$, and its constant term is $1$.

## Proof

Let $S_x=\{\alpha_1,\ldots,\alpha_s\}$ be the multiset of
eigenvalues of $F_x$ on $\mathcal G_{0,\bar x}$, counted with
multiplicity. By [def-wf-iota-real] the multiset
$\iota(S_x)$ is stable under complex conjugation. The eigenvalues
of $F_x$ on $\mathcal G^{\otimes k}_{0,\bar x}$ are the
$k$-fold products $\alpha_{i_1}\cdots\alpha_{i_k}$ ([p-linear-spectra]), and the
multiset of their $\iota$-images is again conjugation-stable, which
proves (i). For (ii), with $k=2k'$ even, the elementary formal
identity

$$
\det(1-tM)^{-1}=\exp\Bigl(\sum_{n\ge1}\operatorname{Tr}(M^n)\frac{t^n}{n}\Bigr)
$$

(valid for every endomorphism $M$ of finite rank; a power-series
identity, per the README allowance for elementary infinite-series
calculus) gives, for the operator $M=F_x$ on
$\mathcal G^{\otimes k}_{0,\bar x}$,

$$
\operatorname{Tr}(M^n)
=\operatorname{Tr}\bigl((F_x^n)^{\otimes k}\bigr)
=\operatorname{Tr}(F_x^n)^{k},
$$

because the eigenvalues of $M^n$ are the $k$-fold products
$\alpha_{i_1}^n\cdots\alpha_{i_k}^n$ and
$\sum_{i_1,\ldots,i_k}\alpha_{i_1}^n\cdots\alpha_{i_k}^n= \bigl(\sum_i\alpha_i^n\bigr)^k$. Since the conjugate of
$\iota(S_x)$ is $\iota(S_x)$ itself, the number
$\iota(\operatorname{Tr}(F_x^n))$ is real, so

$$
\iota(\operatorname{Tr}(M^n))
=\iota(\operatorname{Tr}(F_x^n))^{2k'}\ge0,
$$

and every coefficient of the exponential series is a finite sum of
products of nonnegative reals, hence nonnegative; the constant term
is $1$.
