+++
id = "def-trf-local-term"
kind = "definition"
title = "Local term of a correspondence"
order = 2310
uses = ["def-trf-admissibility", "def-trf-coefficient-conventions", "def-trf-correspondence", "def-trf-dualizing-complex", "def-trf-fixed-scheme", "def-trf-integration", "def-trf-trace-class", "def-weil-finite-field-fiber", "def-weil-scheme-morphism-properties", "prop-functor-package", "thm-trf-dualizing-complex-composition", "thm-trf-frobenius-fixed-points"]
+++
Fix the global finite-field datum
$p,a,q,k_0,k$ of [def-weil-finite-field-fiber] (so $k$ is an algebraic
closure of $k_0$) and the coefficient
conventions, put $s=\Spec k$, and let $E$ be a separated finite-type
$s$-scheme. Throughout, the structure morphisms of $E$ and of the
open-and-closed subschemes of $E$ considered below are assumed
exceptionally admissible in the sense of [def-trf-admissibility], so
that their dualizing complexes of [def-trf-dualizing-complex] are
defined.

*Restricted sections.* Let $\sigma:A_E\to\omega_{E,A}$ be a section
(a morphism in $D(E,A)$), and let $j_B:B\hookrightarrow E$ be the
inclusion of an open-and-closed subscheme. The *restriction* of
$\sigma$ to $B$ is

$$
j_B^*\sigma:\;
A_B\xrightarrow{\ \sim\ }
Lj_B^*A_E
\xrightarrow{Lj_B^*\sigma}
Lj_B^*\omega_{E,A}
\longrightarrow\omega_{B,A},
$$

the last arrow being the canonical identification
$Lj_B^*\omega_{E,A}\cong Rj_B^!\omega_{E,A}\cong\omega_{B,A}$
obtained from the equality $Rj_B^!\cong Lj_B^*$ for the open immersion
$j_B$ (the purity clause of the six-operations package
[prop-functor-package], item (6), in relative dimension $0$) and the
composition isomorphism of [thm-trf-dualizing-complex-composition]
applied to $j_B$. This restricted section is defined for every
open-and-closed $B$, whether or not $B$ (or $E$) is proper over $s$.

*Local terms.* If moreover $B$ is proper over $s$, the *local term*
of $\sigma$ on $B$ is

$$
\operatorname{LT}_B(\sigma):=\int_B j_B^*\sigma\in A,
$$

the integral of [def-trf-integration]; properness of $B$ is needed
only for this scalar integral, and the ambient $E$ need not be proper.

*Endocorrespondences.* Let $c$ be an admissible correspondence in the
sense of [def-trf-correspondence], with
$u:Lc_2^*K\to Rc_1^!K$ and fixed scheme
$F=\operatorname{Fix}(c)$ of [def-trf-fixed-scheme], and let
$\operatorname{Tr}_c(u):A_F\to\omega_{F,A}$ be its trace class of
[def-trf-trace-class]. For an open-and-closed $B\subseteq F$, proper
over $s$, put

$$
\operatorname{LT}_B(u):=\operatorname{LT}_B\bigl(\operatorname{Tr}_c(u)\bigr)
=\int_B j_B^*\operatorname{Tr}_c(u)\in A;
$$

$F$ itself need not be proper. In particular, when $F$ is proper over
$s$ and has finitely many open-and-closed components
$\beta\in\pi_0(F)$ in the sense of [def-trf-fixed-scheme], each $\beta$
is open-and-closed in $F$ and proper over $s$, and we write

$$
\operatorname{Tr}_c(u)|_\beta:=j_\beta^*\operatorname{Tr}_c(u):
A_\beta\longrightarrow\omega_{\beta,A},
\qquad
\operatorname{LT}_\beta(u):=
\int_\beta\bigl(\operatorname{Tr}_c(u)|_\beta\bigr)\in A
$$

for the *local term* of $u$ at $\beta$.

*Point components.* If $\bar x$ is a point of $F$ such that $\{\bar x\}$
is open in $F$ and the open-and-closed subscheme $B_{\bar x}\subseteq F$
with underlying set $\{\bar x\}$ is reduced, then
$B_{\bar x}\simeq\Spec k$ ($k$ being algebraically closed and
$B_{\bar x}$ of finite type over $k$), so $B_{\bar x}$ is proper over
$s$, and we write
$\operatorname{LT}_{\bar x}(u):=\operatorname{LT}_{B_{\bar x}}(u)$,
the local term on the reduced open-and-closed point component of
$\bar x$. This applies to every Frobenius fixed point: for the
Frobenius correspondence $c=(\operatorname{id}_X,\Phi^m)$ on
$X=X_0\times_{k_0}k$, with $X_0$ of finite type over $k_0$ and $\Phi$
the $q$-power scheme Frobenius, the fixed
scheme is the disjoint union of reduced points $\Spec k$, one for each
$y\in X_0(\mathbf F_{q^m})$, by [thm-trf-frobenius-fixed-points], and
$\operatorname{LT}_{\bar y}(u)=\operatorname{LT}_y(u)$ denotes the local
term on the component indexed by $y$.
