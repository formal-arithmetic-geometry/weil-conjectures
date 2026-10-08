+++
id = "lem-weil-stratum-ambient-hom"
kind = "lemma"
title = "Internal Hom from extension along a stratum"
order = 2069
uses = ["def-weil-derived-pullback-tensor-hom", "def-weil-open-closed-recollement", "lem-exc-closed-ambient"]
+++
Let $s:S\hookrightarrow X$ be a locally closed immersion. On either
of the two finite-coefficient sites, and on the ambient derived
categories, there is a natural isomorphism

$$
R\mathcal Hom_X(Rs_!P,M)
\cong Rs_*R\mathcal Hom_S(P,Rs^!M).
$$

No constructible-preservation or biduality assertion is assumed.

## Proof

Factor $s$ into an open and a closed immersion. The adjunctions of
[def-weil-open-closed-recollement], [lem-exc-closed-ambient] construct
$Rs^!$ as their composite. Extension by zero for an open or closed
immersion is exact, and its stalkwise description gives, for all
complexes, $Q\otimes^LRs_!P=Rs_!(s^*Q\otimes^LP)$; use flat
resolutions to derive the tensor product. For every test complex
$Q$ on $X$, the adjunctions and the internal Hom of
[def-weil-derived-pullback-tensor-hom] give

$$
\begin{aligned}
\operatorname{Hom}_X(Q,R\mathcal Hom_X(Rs_!P,M))
&=\operatorname{Hom}_X(Rs_!(s^*Q\otimes^LP),M)\\
&=\operatorname{Hom}_S(s^*Q\otimes^LP,Rs^!M)\\
&=\operatorname{Hom}_X(Q,Rs_*R\mathcal Hom_S(P,Rs^!M)).
\end{aligned}
$$

Yoneda proves the assertion. The maps are defined by evaluation and
the adjunction counits, so the identity is compatible with both.
