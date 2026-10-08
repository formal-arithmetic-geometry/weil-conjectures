+++
id = "sk-cor-picard-degree-g"
kind = "section"
title = "The degree of the dictionary"
order = 744
uses = ["sec-abelian-varieties", "sk-def-av-jacobian", "sk-thm-picard-rr"]
lean = ["AlgebraicGeometry.Scheme.degree_eq_genus"]
+++
*Corollary (sketch).*

Let $X$ be a smooth projective curve of genus $g$ with
$H^0(X,\cO_X)=k$ (e.g. $X$ geometrically integral, or $k$ separably
closed; without it the statement fails: $\mathbf P^1_{\mathbf C}$ over
$k=\mathbf R$, $K=\mathbf C$) and $\cL$ a line
bundle on $X_K$ ($K/k$ any field extension) with $h^0(X_K,\cL)=1$
and $H^q(X_K,\cL)=0$ for $q>0$. Then

$$
\deg(\cL)=\chi(\cL)-\chi(\cO_{X_K})=1-(1-g)=g.
$$

This is the exact instance of Riemann–Roch used in the
zero-scheme dictionary ([sk-lem-picard-zero-dictionary]).

## Proof

The vanishing gives $\chi=h^0=1$. By flat base change
$H^0(X_K,\cO_{X_K})=K$ and $h^1(X_K,\cO_{X_K})=g$, so $X_K$ satisfies
the hypotheses of [sk-thm-picard-rr], and (RR) gives
$\chi(\cO_{X_K})=1-g$ and $\chi(\cL)=\deg\cL+\chi(\cO_{X_K})$;
hence $\deg\cL=g$.
