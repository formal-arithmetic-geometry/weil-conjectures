+++
id = "lemma-weil-pbc-projection-formula-totalization"
kind = "lemma"
title = "Signed totalization of the perfect formula"
order = 1267
uses = ["def-weil-pbc-projection-formula-arrows", "lemma-weil-pbc-projection-formula-projective-summand"]
+++
For a bounded finite-projective complex $F^\bullet$, the total arrows
$\pi_{h,E,F}$ and $\rho_{h,E,F}$ are inverse isomorphisms.

## Proof

Choose a complex representing $Rh_*E$. On a homogeneous tensor
$x\otimes y$ with $x$ of degree $a$, both total complexes use

$$
d(x\otimes y)=d(x)\otimes y+(-1)^a x\otimes d_F(y).
$$

Naturality of $\pi_{F^r}$ in a map of finite projective modules and uniqueness
of its inverse give naturality of $\rho_{F^r}$. Apply these two naturality
statements to every differential $d_F^r:F^r\to F^{r+1}$. They say the term
maps commute with the horizontal differentials; their degree zero says they
commute with the signed vertical differentials. Hence their finite
totalizations are chain maps. On every bidegree the two composites are the
identities proved in the summand lemma. Finite totalization preserves these
equalities, so

$$
\rho_{h,E,F}\pi_{h,E,F}=1,
\qquad \pi_{h,E,F}\rho_{h,E,F}=1.
$$
