+++
id = "sk-lem-orthogonality"
kind = "section"
title = "Orthogonality"
order = 2673
lean = ["AddChar.sum_eq_ite", "AddChar.sum_mulShift"]
uses = ["sk-def-char"]
+++
*Lemma (sketch).*

$\sum_{x\in k_0}c\,\psi_a(x)=cq$ if $\psi_a=1$, and $0$ otherwise; and
$\sum_{y\in\mathbf F_{q^n}}\psi_n((x-x')y)=q^n$ if $x=x'$, and $0$ otherwise.
(Blueprint lem:fd-character-orthogonality,
lem:fd-additive-orthogonality.)

## Proof

If $\psi_a\neq1$ choose $y$ with $\psi_a(y)\neq1$; translation is a
bijection, so $S=\psi_a(y)S$, hence $S=0$. The second identity is the first
applied to $y\mapsto\psi_n((x-x')y)$, which is nontrivial exactly when
$x\neq x'$. The same sums separate the $\psi_a$ for distinct $a$, so every
nondegenerate character of $k_0$ is some $\psi_a$ (not used later).

Uses: [sk-def-char]
