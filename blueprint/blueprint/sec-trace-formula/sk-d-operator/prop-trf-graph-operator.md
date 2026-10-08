+++
id = "prop-trf-graph-operator"
kind = "theorem"
title = "Graph construction of the global operator"
order = 2293
tags = ["latex:proposition"]
uses = ["def-compact-support-direct-image-detailed", "def-trf-global-operator", "def-weil-derived-direct-image"]
+++
Let $(h,v)$ be a graph correspondence with $h$ proper. The global
operator $T_c(v)$ of [def-trf-global-operator] is the composite

$$
R\Gamma_c(X,K)\longrightarrow R\Gamma_c(X,Lh^*K)
\xrightarrow{R\Gamma_c(X,v)}R\Gamma_c(X,K),
$$

where the first arrow is induced by the unit
$K\to Rh_*Lh^*K$ and the canonical identification
$Rh_*\simeq Rh_!$. It is functorial in $(K,v)$, additive in
distinguished triangles, and compatible with composition of proper
endomorphisms.

## Proof

For the graph correspondence $c_1=\operatorname{id}_X$ and $c_2=h$,
the display of [def-trf-global-operator] reads

$$
\begin{aligned}
R\Gamma_c(X,K)&\xrightarrow{\eta^*_h}
R\Gamma_c(X,Rh_*Lh^*K)
\xrightarrow{\ \sim\ }R\Gamma_c(X,Lh^*K)\\
&\xrightarrow{R\Gamma_c(X,v)}
R\Gamma_c(X,K),
\end{aligned}
$$

where the second arrow is the identification of
[def-weil-derived-direct-image] for the proper $h$
($Rh_*\simeq Rh_!$ composed with the compact-support direct-image
identification of [def-compact-support-direct-image-detailed]), and the
last arrow is the counit of the identity adjunction. This is the
displayed composite. Functoriality, additivity over triangles, and
compatibility with composition are the corresponding properties of the
unit-counit calculus, of $R\Gamma_c$, and of the identifications
quoted above.
