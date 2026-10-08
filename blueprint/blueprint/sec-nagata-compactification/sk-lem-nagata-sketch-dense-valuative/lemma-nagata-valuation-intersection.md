+++
id = "lemma-nagata-valuation-intersection"
kind = "lemma"
title = "Intersection with a dominating valuation ring"
order = 275
lean = ["ValuationSubring.comap_eq_of_toLocalSubring_le"]
+++
Let $A$ be a valuation ring with fraction field $K$, let
$K\hookrightarrow L$ be a field extension, and let $B\subseteq L$ be a
valuation ring dominating the image of $A$. Then

$$
K\cap B=A
$$

inside $L$.

## Proof

The inclusion $A\subseteq K\cap B$ follows because $B$ contains the image
of $A$. Conversely, let $x\in K\cap B$. If $x\notin A$, the valuation-ring
property of $A$ gives $x^{-1}\in A$, and in fact
$x^{-1}\in\mathfrak m_A$: otherwise $x^{-1}$ would be a unit of $A$ and
$x$ would belong to $A$. Since $B$ dominates $A$, the image of
$\mathfrak m_A$ lies in $\mathfrak m_B$. But $x\in B$ and
$x^{-1}\in\mathfrak m_B$ would imply
$1=xx^{-1}\in\mathfrak m_B$, a contradiction. Thus $x\in A$, proving
$K\cap B\subseteq A$ and hence the asserted equality.
