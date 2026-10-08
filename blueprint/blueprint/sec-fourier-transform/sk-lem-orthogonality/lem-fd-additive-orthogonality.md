+++
id = "lem-fd-additive-orthogonality"
kind = "lemma"
title = "Additive orthogonality over $\\mathbf F_{q^n}$"
order = 2675
lean = ["AddChar.sum_mulShift"]
uses = ["def-fd-additive-character"]
+++
For the nondegenerate additive character $\psi_n(x)=\psi(\operatorname{Tr}_{\mathbf F_{q^n}/k_0}(x))=\Psi(\operatorname{Tr}_{\mathbf F_{q^n}/\mathbf F_p}(x))$ of $\mathbf F_{q^n}$,

$$
\sum_{y\in\mathbf F_{q^n}}\psi_n\bigl((x-x')y\bigr)
=\begin{cases}q^n,&x=x',\\0,&x\ne x'.\end{cases}
$$

## Proof

For $x=x'$ every summand is $\psi_n(0)=1$, giving the sum $q^n$. Otherwise multiplication by $x-x'$ is a bijection of the additive group of $\mathbf F_{q^n}$, and translating the sum by an element $y_0$ on which $\psi_n$ is nontrivial (it is nontrivial because $\operatorname{Tr}_{\mathbf F_{q^n}/k_0}$ is surjective and $\psi$ is nontrivial) multiplies the sum by $\psi_n(y_0)\neq1$; hence the sum vanishes.
