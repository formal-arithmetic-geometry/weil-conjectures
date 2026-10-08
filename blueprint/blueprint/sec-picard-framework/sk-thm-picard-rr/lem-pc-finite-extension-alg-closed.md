+++
id = "lem-pc-finite-extension-alg-closed"
kind = "lemma"
title = "Finite extensions of algebraically closed fields"
order = 727
uses = ["def-pc-field-tower"]
+++
Let $\Omega$ be an algebraically closed field and $\Omega\subseteq K$ a
finite field extension. Then $K=\Omega$.

## Proof

Let $\alpha\in K$. The minimal polynomial $m_\alpha\in\Omega[T]$ is
irreducible; over the algebraically closed field it has a root, and an
irreducible polynomial with a root is linear, so $\deg m_\alpha=1$ and
$\alpha\in\Omega$. (We use the standard irreducible-polynomial-with-a-root
argument: $m_\alpha=(T-\beta)q(T)$ with $\beta\in\Omega$ and $m_\alpha$
irreducible forces $q$ constant.)
