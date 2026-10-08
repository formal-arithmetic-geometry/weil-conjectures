+++
id = "lem-pc-kbar-pure-insep"
kind = "lemma"
title = "The algebraic closure over a separably closed field"
order = 750
uses = ["def-pc-field-tower", "def-pc-separably-closed", "lem-pc-sepclosed-finite-sep-trivial"]
+++
Let $k$ be a separably closed field
of characteristic $p$, and let $\alpha\in\bar k$ be algebraic over $k$.
Then there is an $n\ge0$ with $\alpha^{p^n}$ separable over $k$; hence
$\bar k/k$ is purely inseparable.

## Proof

Let $K=k(\alpha)$ (finite over $k$). Let $L$ be the separable closure
of $k$ inside $K$, i.e. the maximal separable subextension (standard:
among the subextensions $k\subseteq k'\subseteq K$ with $k'/k$ finite
separable there is a maximal one, obtained by compositum).
Then $K/L$ is purely inseparable: for a finite extension in
characteristic $p$ this is the standard fact that a finite extension is
the compositum of a separable and a purely inseparable subextension
(the tower $K/k$ decomposes: the separable part $L$, and for
$\beta\in K$ the minimal polynomial over $L$ is $T^{p^f}-c$, a purely
inseparable polynomial: this is the classical normal-separable
devissage; we use it as standard field theory). Let
$[K:L]=p^e$. For every $\beta\in K$, $\beta^{p^e}\in L$: indeed the
minimal polynomial $T^{p^f}-c$ of $\beta$ over $L$ has $f\le e$, and
$\beta^{p^e}=c^{p^{e-f}}\in L$.
Apply this to $\beta=\alpha$: $\alpha^{p^e}\in L$, which is separable
over $k$; take $n=e$. The last assertion: since $\bar k$ is
generated over $k$ by its algebraic elements and $\alpha^{p^n}$ is
separable for some $n$, the field $\bar k$ is the union of its
subfields $k(\alpha)$ with each $\alpha^{p^n}\in k^{sep}=k$ (by
[lem-pc-sepclosed-finite-sep-trivial] the separable elements are
in $k$): every element of $\bar k$ lies in $k$ after taking
$p^n$-th powers, i.e. $\bar k/k$ is purely inseparable.
