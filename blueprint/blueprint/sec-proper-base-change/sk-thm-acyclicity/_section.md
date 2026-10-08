+++
id = "sk-thm-acyclicity"
kind = "section"
title = "Acyclicity criterion"
order = 1065
+++
*Theorem (sketch).*

Let $v$ be a left exact functor between abelian categories with
enough injectives. If $F\to I^\bullet$ is a resolution by
$v$-acyclic objects (i.e. $R^qvI^m=0$ for $q>0$), then

$$
\mathcal H^q(vI^\bullet)\xrightarrow{\ \sim\ }R^qvF :
$$

the cohomology of a termwise-acyclic complex computes the derived
functor.

## Proof

Induct on $q$ by breaking $F\to I^\bullet$ into the short exact
sequences $0\to Z^m\to I^m\to Z^{m+1}\to0$ ($Z^0=F$): their long
exact sequences and the vanishing $R^qvI^m=0$ ($q>0$) give
$R^qvZ^{m}\cong R^{q-1}vZ^{m+1}$ for $q\ge2$ and identify
$R^1vZ^m$ with $\operatorname{coker}(vI^m\to vZ^{m+1})$;
dimension-shifting then matches $\mathcal H^q(vI^\bullet)$ with
$R^qvF$. No spectral sequence is needed — this is why it is
separated from [sk-thm-groth-ss].
