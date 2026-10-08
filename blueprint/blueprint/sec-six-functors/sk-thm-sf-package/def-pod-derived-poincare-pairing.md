+++
id = "def-pod-derived-poincare-pairing"
kind = "definition"
title = "Derived Poincare pairing"
order = 2251
uses = ["def-pod-coefficient-dual-on-x"]
+++
In the Poincare duality conventions of this chapter (the fixed setting), let $\Lambda\in\{A,\mathcal O_E,E,\overline{\mathbf Q}_{\ell}\}$ and let $K\in D^b_{ctf}(X,\Lambda)$ be perfect over $\Lambda_X$ (the case $\Lambda=A$ is the finite stage; the other coefficients are its transports). The *derived Poincare pairing* is the composite

$$
\beta _K:\   R\Gamma _c(X,K)\otimes _\Lambda ^LR\Gamma \bigl(X,K^\vee (d)\bigr)[2d] \longrightarrow \Lambda,
$$

$$
\begin{array}{lll} R\Gamma _c(X,K)\otimes _\Lambda ^LR\Gamma \bigl(X,K^\vee (d)\bigr)[2d] & \xrightarrow {\  \smile _c\  }&  R\Gamma _c\bigl(X,K\otimes ^L_{\Lambda _X}K^\vee (d)\bigr)[2d]\\ & \xrightarrow {R\Gamma _c(\operatorname {ev}_K(d))[2d]}&  R\Gamma _c\bigl(X,\Lambda _X(d)\bigr)[2d]\\ & \xrightarrow {\  \operatorname {Tr}^{\mathrm{sm}}_{a_X,\Lambda }\  }&  \Lambda, \end{array}
$$

where $\smile _c$ is the mixed-support cup product, $\operatorname {ev}_K$ is the evaluation of Definition 9.5, and $\operatorname {Tr}^{\mathrm{sm}}_{a_X,\Lambda }$ is the normalized smooth trace of the purity chapter for the structure morphism $a_X$, i.e. the counit of $Ra_{X!}\dashv Ra_X^!$ through the canonical orientation $\eta _X$. None of these ingredients uses properness: the cup product and the trace only involve $Ra_{X!}$, $Ra_{X*}$ and $Ra_X^!$ for the separated finite-type smooth morphism $a_X$.
