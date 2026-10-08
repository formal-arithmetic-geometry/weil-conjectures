+++
id = "def-pod-dual-tate-datum"
kind = "definition"
title = "Dual and Tate Weil data"
order = 2424
uses = ["def-trf-scheme-frobenius"]
lean = ["AlgebraicGeometry.ProEtale.WeilComplex"]
+++
In the Poincare duality conventions of this chapter (the fixed setting), strict Weil complex: a perfect $K\in D^b_{ctf}(X,A)$ with $\varphi _K:Lg_\gamma ^*K\xrightarrow {\sim }K$, in the notation of Definition 7.2 and of the geometric-Frobenius datum of the purity chapter. Let $\varphi _A:Lg_\gamma ^*A_X\xrightarrow {\sim } A_X$ be the canonical Weil structure on the constant coefficient object, and let $\tau _r:Lg_\gamma ^*A_X(r)\xrightarrow {\sim }A_X(r)$ be the Tate datum of the purity chapter, on which geometric Frobenius acts by the scalar $q^{-r}$. The *contragredient datum* on the coefficient dual is the typed composite

$$
\begin{gathered}
\varphi _{K^\vee }:\   Lg_\gamma ^*R\mathcal Hom_X(K,A_X) \\
\xrightarrow {\  \sim \  } R\mathcal Hom_X\bigl(Lg_\gamma ^*K,Lg_\gamma ^*A_X\bigr) \\
\xrightarrow {R\mathcal Hom(\operatorname {id},\varphi _A)} R\mathcal Hom_X\bigl(Lg_\gamma ^*K,A_X\bigr) \\
\xrightarrow {R\mathcal Hom(\varphi _K^{-1},\operatorname {id})} R\mathcal Hom_X(K,A_X),
\end{gathered}
$$

and the datum on the twisted dual is $\varphi _{K^\vee (r)}=\varphi _{K^\vee }\otimes \tau _r$, with the scalar $q^{-r}$ on $A_X(r)$ (hence $q^r$ on $A_X(-r)$). For $K=\Lambda_X$ the constant sheaf with its canonical datum, the contragredient datum corresponds to the canonical datum under the canonical identification $(\Lambda_X)^\vee\cong\Lambda_X$, and the resulting $F$-operators are the iterated global geometric Frobenius operators of chap:trace-formula.
