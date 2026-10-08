+++
id = "def-wf-iota-real"
kind = "definition"
title = "$\\iota$-real and $\\iota$-realizable Weil sheaves"
order = 2589
uses = ["def-weil-constructible-heart", "def-weil-punctual-weights", "def-weil-weil-sheaf-complex"]
+++
Let $X_0$ be a separated finite-type $k_0$-scheme, fix
$\iota:\Qlb\xrightarrow{\sim}\mathbf C$ as in
[def-weil-punctual-weights], and let $\mathcal F$ be a
constructible
Weil sheaf on $X_0$, with the
stalk Frobenius modules $(V_x,F_x)$ of
[def-weil-punctual-weights]. Reality is a pointwise condition on
those modules, so the definition is stated for constructible sheaves; the
lisse case is the classical one, and is the case in which the notion of
realizability below is applied. The *local characteristic
factor* of $\mathcal F$ at a closed point $x$ is

$$
P_x(T):=\prod_{\alpha\in S_x}(1-\alpha T)=\det(1-TF_x\mid V_x),
$$

where $S_x$ is the spectrum of $F_x$ counted with multiplicity.
The sheaf $\mathcal F$ is *$\iota$-real* if
$\iota(P_x(T))\in\mathbf R[T]$ for every closed point $x\in|X_0|$;
equivalently, the multiset of complex Frobenius eigenvalues is stable
under complex conjugation at every closed point. The sheaf $\mathcal F$
is *$\iota$-realizable* if it is a direct summand (in the category
of Weil sheaves) of an $\iota$-real lisse Weil sheaf
(*Deligne, Weil II, (1.2.13)*).
