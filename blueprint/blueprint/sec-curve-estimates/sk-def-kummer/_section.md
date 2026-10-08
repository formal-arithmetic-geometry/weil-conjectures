+++
id = "sk-def-kummer"
kind = "section"
title = "The Kummer sequence"
order = 873
uses = ["sk-def-curve"]
lean = ["AlgebraicGeometry.Scheme.kummerSequence"]
+++
*Definition (sketch).*

For $n\ge1$ and $C$ as in [sk-def-curve], the *Kummer
sequence* is the sequence of étale sheaves on $C$

$$
0\longrightarrow\mu_n\longrightarrow\mathbb G_m
\xrightarrow{\ \omega\mapsto\omega^n\ }\mathbb G_m\longrightarrow0
$$

where $\mu_n=\ker(n)$ is the sheaf of $n$-th roots of unity. Its
exactness is [sk-prop-kummer-exact] and is *not* part of the
definition.

Uses: [sk-def-curve]
