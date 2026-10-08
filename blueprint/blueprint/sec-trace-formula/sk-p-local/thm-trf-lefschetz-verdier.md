+++
id = "thm-trf-lefschetz-verdier"
kind = "theorem"
title = "Lefschetz–Verdier trace comparison"
order = 2350
uses = ["def-trf-admissibility", "def-trf-categorical-trace", "def-trf-coefficient-conventions", "def-trf-correspondence", "def-trf-fixed-scheme", "def-trf-global-operator", "def-trf-local-term", "def-weil-finite-field-fiber", "def-weil-scheme-morphism-properties", "lem-trf-global-operator-perfect", "lem-trf-integration-component-sum", "thm-trf-fixed-point-localization"]
+++
Fix the global finite-field datum
and the coefficient
conventions, $A=A_{E,n}$, $s=\Spec k$, and let $X$ be a
proper finite-type scheme.
Let $c=(c_1,c_2):C\to X\times_sX$ be an
admissible
cohomological correspondence with
$c_2$ proper and with
fixed scheme
$F=\operatorname{Fix}(c)$ proper over $s$ and with finitely many
open-and-closed components. Let $K\in D^b_{ctf}(X,A)$. Then

$$
\operatorname{tr}_A\bigl(T_c(u)\mid R\Gamma_c(X,K)\bigr)
=
\sum_{\beta\in\pi_0(F)}
\operatorname{LT}_\beta(u)
\quad\text{in }A,
$$

where $T_c(u)$ is the
global operator of
[def-trf-global-operator],
$\operatorname{tr}_A$ the
categorical trace, and the
$\operatorname{LT}_\beta(u)$ are the
local terms. Equivalently, the
categorical trace of the global operator equals the sum of the local
terms over the fixed points. (Source: the Lefschetz–Verdier trace
formula for cohomological correspondences; see Milne, Lectures on Etale
Cohomology, Section 29 (the Lefschetz fixed-point formula for
nonconstant sheaves), with Section 25 for the constant-sheaf case, and
$SGA5$, Expose III. The comparison is assembled here from the
trace-class machinery, the fixed-point localization theorem and the
perfectness of the global operator; see the proof.)

## Proof

The categorical trace on the left is defined because the global
operator $T_c(u)$ of [def-trf-global-operator] is a morphism of
$D^b_{\mathrm{fin}}(A)$, hence an endomorphism of a perfect complex,
by [lem-trf-global-operator-perfect]. With this, the
localization theorem [thm-trf-fixed-point-localization] gives

$$
\operatorname{tr}_A(T_c(u)\mid R\Gamma_c(X,K))
=\int_F\operatorname{Tr}_c(u).
$$

The component integration formula
[lem-trf-integration-component-sum] (applicable since each component
$\beta$, being closed in the proper $F$, is proper over $s$) rewrites
the right side as

$$
\sum_{\beta\in\pi_0(F)}
\int_\beta\bigl(\operatorname{Tr}_c(u)|_\beta\bigr).
$$

Each summand is $\operatorname{LT}_\beta(u)$ by
[def-trf-local-term], which proves the comparison.
