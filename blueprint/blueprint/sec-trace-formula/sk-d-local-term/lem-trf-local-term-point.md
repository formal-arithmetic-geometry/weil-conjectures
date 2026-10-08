+++
id = "lem-trf-local-term-point"
kind = "lemma"
title = "The local term at a point component"
order = 2337
uses = ["def-trf-admissibility", "def-trf-coefficient-conventions", "def-trf-correspondence", "def-trf-dualizing-complex", "def-trf-fixed-scheme", "def-trf-integration", "def-trf-local-term", "def-trf-trace-class", "def-weil-scheme-morphism-properties", "lem-trf-integration-linear", "prop-functor-package", "prop-trf-trace-class-unconditional"]
+++
Fix the coefficient
conventions, let $c$ be an
admissible correspondence with
fixed scheme $F$ over $s=\Spec k$ (not necessarily proper), and let
$\beta\subseteq F$ be an open-and-closed subscheme with
$\beta\simeq\Spec k$, finite etale over $s$ in relative dimension
$0$ (for instance a component $\beta\in\pi_0(F)$ of this form when
$F$ is proper with finitely many open-and-closed components, or the
reduced point component $B_{\bar x}$ of a point $\bar x$ of $F$). Then
the local term
$\operatorname{LT}_\beta(u)=\int_\beta(\operatorname{Tr}_c(u)|_\beta)$
of [def-trf-local-term], where
$\operatorname{Tr}_c(u)|_\beta=j_\beta^*\operatorname{Tr}_c(u)$, is
the element of $A$ corresponding to
the trace class
$\operatorname{Tr}_c(u)|_\beta$ under the canonical identification

$$
\operatorname{Hom}_{D(\beta,A)}\bigl(A_\beta,\omega_{\beta,A}\bigr)
\cong\operatorname{End}_{D(A)}(A)\cong A
$$

of the point case $\beta\simeq\Spec k$. In particular this computes
$\operatorname{LT}_{\bar x}(u)=\operatorname{LT}_{B_{\bar x}}(u)$ at
every point $\bar x$ with reduced open-and-closed point component
$B_{\bar x}$.

## Proof

The trace class
$\operatorname{Tr}_c(u)$ and hence its restriction
$\operatorname{Tr}_c(u)|_\beta$ of [def-trf-local-term] are
defined for the admissible $c$ by
[prop-trf-trace-class-unconditional]. Being isomorphic to $\Spec k$, the open-and-closed subscheme $\beta$
of the fixed scheme of [def-trf-fixed-scheme] is a
separated finite-type
proper $s$-scheme, and (as in [def-trf-local-term]) it is taken with structure morphism $a_\beta$ admissible in
the sense of [def-trf-admissibility], and the purity clause of
[prop-functor-package] in relative dimension $0$ identifies
$\omega_{\beta,A}=Ra_\beta^!A_s$ of
[def-trf-dualizing-complex] with $A_\beta$, so that
$\operatorname{Hom}_{D(\beta,A)}(A_\beta,\omega_{\beta,A})\cong \operatorname{End}_{D(A)}(A)\cong A$.
For $\tau:A_\beta\to\omega_{\beta,A}$ the integration is the
composite $A\xrightarrow{\eta^*}R\Gamma(\beta,A_\beta) \xrightarrow{R\Gamma(\tau)}R\Gamma(\beta,\omega_{\beta,A}) \xrightarrow{\varepsilon_{a_\beta}}A$ of
[def-trf-integration]. For $\tau=\operatorname{id}_{A_\beta}$
under the identification $\omega_{\beta,A}\cong A_\beta$, the middle
arrow is the identity of $R\Gamma(\beta,A_\beta)$ and the composite
of the first and last arrows is the composite of the unit and the
counit of the adjunction $Ra_{\beta!}\dashv Ra_\beta^!$ of
[def-trf-admissibility], which is the identity of $A$ by the
triangle identity of the adjunction; since the integration is
$A$-linear by [lem-trf-integration-linear], it is the identity
map on all of $A$. Applying this to
$\tau=\operatorname{Tr}_c(u)|_\beta$ gives the last assertion, by the
definition of the local term in [def-trf-local-term].
