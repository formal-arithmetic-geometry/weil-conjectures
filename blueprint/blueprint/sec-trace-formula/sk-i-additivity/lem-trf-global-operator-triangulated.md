+++
id = "lem-trf-global-operator-triangulated"
kind = "lemma"
title = "The global operator is triangulated in the coefficient"
order = 2352
uses = ["def-trf-admissibility", "def-trf-global-operator", "lem-trf-global-operator-naturality", "prop-trf-compact-support-perfectness"]
+++
In the setting of [def-trf-global-operator], let
$K'\to K\to K''\to K'[1]$ be a distinguished triangle in
$D^b_{ctf}(X,A)$ and let $(u',u,u'')$ be a morphism of the
corresponding triangles of the functors $Lc_2^*$ and $Rc_1^!$.
Then the global operators of [def-trf-global-operator] fit into a
morphism of distinguished triangles

$$
\begin{array}{ccc}
R\Gamma_c(X,K')&\xrightarrow{\ T_c(u')\ }&R\Gamma_c(X,K')\\
\Big\downarrow&&\Big\downarrow\\
R\Gamma_c(X,K)&\xrightarrow{\ T_c(u)\ }&R\Gamma_c(X,K)\\
\Big\downarrow&&\Big\downarrow\\
R\Gamma_c(X,K'')&\xrightarrow{\ T_c(u'')\ }&R\Gamma_c(X,K'').
\end{array}
$$

## Proof

By [def-trf-global-operator] the global operator is the composite
of the counit of the adjunction $Rc_{2,!}\dashv Rc_2^!$, the
identification $R\Gamma_c(X,Rc_{2,*}Lc_2^*K)\cong R\Gamma_c(C,Lc_2^*K)$, the map $R\Gamma_c(C,u)$ and the
identification $R\Gamma_c(C,Rc_1^!K)\cong R\Gamma_c(X,Rc_{1,!}Rc_1^!K)$
with its counit. Each of these constructions is a natural
transformation of exact functors in the coefficient object: the
functors $Lc_2^*$, $Rc_1^!$, $Rc_{i,*}$, $Rc_{i,!}$,
$R\Gamma_c$ are exact (the admissibility of
[def-trf-admissibility] supplies the adjunctions and
[prop-trf-compact-support-perfectness] the perfectness needed for
the compact-support identifications), the units and counits of
adjunctions are natural, and the exchange identifications are
compatible with base change. Hence, the squares commuting by [lem-trf-global-operator-naturality], the composite is compatible with
distinguished triangles, which is the assertion.
