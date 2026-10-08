+++
id = "lemma-weil-pbc-projection-formula-base-change-naturality"
kind = "lemma"
title = "Operator and base-change naturality of the formula"
order = 1274
uses = ["def-weil-pbc-cartesian-square", "def-weil-pbc-projection-formula-arrows"]
+++
The projection-formula arrows are natural in $K$; hence for every
endomorphism $\phi:K\to K$ with reductions $\phi_n:K_n\to K_n$,

$$
Rf_*\phi_n\,\pi_n=\pi_n((Rf_*\phi)\otimes1),
\qquad
((Rf_*\phi)\otimes1)\rho_n=\rho_nRf_*\phi_n.
$$

For a Cartesian square, the following two routes are equal:

$$
\begin{aligned}
Lg^*((Rf_*K)\otimes^LQ)
&\xrightarrow{Lg^*\pi_f}Lg^*Rf_*(K\otimes^LLf^*Q)
\xrightarrow{\operatorname{Ex}_{K\otimes Lf^*Q}}
Rf'_*L(g')^*(K\otimes^LLf^*Q),\\
Lg^*((Rf_*K)\otimes^LQ)
&\xrightarrow{\sim}(Lg^*Rf_*K)\otimes^LLg^*Q
\xrightarrow{\operatorname{Ex}_K\otimes1}
(Rf'_*L(g')^*K)\otimes^LLg^*Q\\
&\xrightarrow{\pi_{f'}}
Rf'_*(L(g')^*K\otimes^LL(f')^*Lg^*Q).
\end{aligned}
$$

The targets are identified by the chosen Cartesian isomorphism.

## Proof

For a map $u:K\to L$, both naturality composites are adjoint to

$$
Lf^*Rf_*K\otimes Lf^*Q
\xrightarrow{\epsilon_K\otimes1}K\otimes Lf^*Q
\xrightarrow{u\otimes1}L\otimes Lf^*Q.
$$

This proves the forward operator equation; conjugation by $\rho_n=\pi_n^{-1}$
gives the second. For base change, expand both exchange maps as unit followed
by counit. After adjunction to $X'$, both displayed routes become

$$
L(g')^*Lf^*Rf_*K\otimes L(g')^*Lf^*Q
\xrightarrow{L(g')^*(\epsilon_K)\otimes1}
L(g')^*K\otimes L(g')^*Lf^*Q.
$$

The Cartesian identification
$L(g')^*Lf^*=L(f')^*Lg^*$ identifies the coefficient factors. Hence the
adjoints, and therefore the two routes, are equal.
