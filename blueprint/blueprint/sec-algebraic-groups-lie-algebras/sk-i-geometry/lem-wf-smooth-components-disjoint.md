+++
id = "lem-wf-smooth-components-disjoint"
kind = "lemma"
title = "Irreducible components of a smooth variety do not meet"
order = 2487
uses = ["lem-sc-regular-local-domain", "lem-wf-affine-noetherian-components"]
+++
Let $X$ be an affine scheme of finite type over a field $k$ whose local
ring at every closed point is regular (for instance a smooth affine
variety). Then any two distinct irreducible components of $X$ are
disjoint. Consequently the (finitely many) irreducible components of $X$
are open and closed, and are its connected components.

## Proof

Write $A=k[X]$. The irreducible components of $X=\operatorname{Spec}A$
are the sets $V(\mathfrak p)$ for the minimal primes $\mathfrak p$ of
$A$, distinct minimal primes giving distinct components. Suppose
$V(\mathfrak p_1)\cap V(\mathfrak p_2)\neq\varnothing$ with
$\mathfrak p_1\neq\mathfrak p_2$ minimal. This intersection is
$V(\mathfrak p_1+\mathfrak p_2)$ with $\mathfrak p_1+\mathfrak p_2$ a
proper ideal, so it is contained in some maximal ideal
$\mathfrak m$, a closed point $x$. The local ring
$A_{\mathfrak m}$ is regular by hypothesis, hence a domain by
[lem-sc-regular-local-domain], so it has a unique minimal prime, namely
$(0)$. But $\mathfrak p_1A_{\mathfrak m}$ and $\mathfrak p_2A_{\mathfrak m}$
are two distinct minimal primes of $A_{\mathfrak m}$, since primes of
the localization correspond to primes of $A$ inside $\mathfrak m$,
compatibly with inclusion. This contradiction shows that distinct
components are disjoint.

There are finitely many components $C_1,\ldots,C_m$ by
[lem-wf-affine-noetherian-components], each closed, pairwise disjoint,
and covering $X$. The complement of $C_j$ is the finite union of the
others, hence closed, so $C_j$ is also open. Each $C_j$ is irreducible,
hence connected, and open and closed, so it is a connected component.
