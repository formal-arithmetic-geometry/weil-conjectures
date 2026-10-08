+++
id = "lem-pc-projective-space-serre-vanishing"
kind = "lemma"
title = "Serre vanishing on projective space over a Noetherian ring"
order = 627
uses = ["def-pc-projective-space-twist", "lem-pc-projective-space-cohomology-bound", "lem-pc-projective-space-twist-cohomology", "lem-pc-projective-space-twist-quotient", "pqf-def-coherent", "pqf-def-cohomology"]
+++
Let $A$ be Noetherian and $\mathcal F$ a
coherent module on
$P=\hyperref[def-pc-projective-space-twist]{\mathbf P^n_A}$.
There is $d_0\ge0$ such that $H^q(P,\mathcal F(d))=0$ for
all $d\ge d_0$ and all $q>0$.

## Proof

For each positive $q$, descend on $q$ to prove eventual vanishing
for every coherent module. For $q>n$, use
[lem-pc-projective-space-cohomology-bound].
Choose $0\to\mathcal K\to\bigoplus_j\mathcal O_P(-m_j) \to\mathcal F\to0$ as in
[lem-pc-projective-space-twist-quotient].
Tensoring by the invertible $\mathcal O_P(d)$ preserves exactness.
In its long exact sequence, from [pqf-def-cohomology], the terms
on either side of $H^q(P,\mathcal F(d))$ are

$$
\bigoplus_j H^q(P,\mathcal O_P(d-m_j)),\qquad
H^{q+1}(P,\mathcal K(d)).
$$

The first vanishes for $d\ge\max_j m_j$ by
[lem-pc-projective-space-twist-cohomology], since $q>0$.
The second vanishes for $d\ge d_{q+1}(\mathcal K)$ by the induction
hypothesis for the coherent kernel. Thus a valid bound in degree
$q$ is $\max(0,\max_j m_j,d_{q+1}(\mathcal K))$, with the maximum
over an empty list of $m_j$ taken as zero.
Take the maximum of the finitely many bounds for $1\le q\le n$.
For $n=0$ the cohomology bound already proves the assertion.
