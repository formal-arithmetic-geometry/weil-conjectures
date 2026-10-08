+++
id = "pqf-lem-associated-sections-localize"
kind = "lemma"
title = "Principal localization of an associated module sheaf"
order = 541
uses = ["pqf-def-coherent"]
+++
Let $A\to B$ be a ring homomorphism, let $M$ be a $B$-module,
and let $a\in A$. For the
associated quasi-coherent sheaf
$\widetilde M$ on $\operatorname{Spec}B$, restriction induces

$$
\Gamma\bigl(\operatorname{Spec}(B\otimes_AA_a),\widetilde M\bigr)
\cong M\otimes_AA_a.
$$

## Proof

Write $b$ for the image of $a$ in $B$. The inverse image of
$D(a)$ is $D(b)=\operatorname{Spec}B_b$, and the associated sheaf
of [pqf-def-coherent] has sections $M_b$ on this principal open.
The universal properties of localization give
$B\otimes_AA_a=B_b$ and $M\otimes_AA_a=M_b$, compatibly with
restriction. These identifications give the formula.
