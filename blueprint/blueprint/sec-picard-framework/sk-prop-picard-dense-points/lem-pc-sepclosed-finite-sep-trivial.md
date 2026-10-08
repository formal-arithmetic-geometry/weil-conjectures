+++
id = "lem-pc-sepclosed-finite-sep-trivial"
kind = "lemma"
title = "Separably closed fields: finite separable extensions are trivial"
order = 748
uses = ["def-pc-separably-closed"]
+++
Let $k$ be a separably closed field.
Then every finite separable field extension $K/k$ is trivial: $K=k$.

## Proof

The extension is finite and separable, hence simple: $K=k[\alpha]$ for some
$\alpha$ (primitive element theorem, classical). Let $m_\alpha\in k[T]$ be
the minimal polynomial of $\alpha$; it is nonconstant and separable, hence
all its roots lie in $k$ (by separably closedness: a separable polynomial
has a root in $k$, and then the quotient $k[T]/(m_\alpha)$ is a field only
if $m_\alpha$ has degree $1$ —indeed $m_\alpha$ being irreducible and
splitting over $k$ forces $\deg m_\alpha=1$). Therefore $\alpha\in k$ and
$K=k$.
