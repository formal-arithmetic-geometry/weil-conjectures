+++
id = "lem-sc-pic-proper-decomposition"
kind = "lemma"
title = "Structure of the Picard group of a proper curve"
order = 888
uses = ["def-sc-curves", "def-sc-pic0", "def-sc-picard-group"]
+++
Let $C$ be a proper smooth connected curve over
algebraically closed $k$. The degree sequence

$$
0\longrightarrow\operatorname{Pic}^0(C)\longrightarrow
\operatorname{Pic}(C)\xrightarrow{\ \deg\ }\mathbf Z\longrightarrow0
$$

splits (the degree map is surjective since a $k$-rational point
gives a degree-one class), hence

$$
\operatorname{Pic}(C)\cong\mathbf Z\oplus\operatorname{Pic}^0(C).
$$

## Proof

The degree map is surjective: a nonempty proper scheme over $k$
has a closed point $P$, whose residue field is finite over $k$,
hence equal to $k$ (Hilbert's Nullstellensatz: *reference:
Stacks Project, Algebra: the Nullstellensatz*), and $\mathcal O([P])$ is a class of degree $1$
([def-sc-pic0]). The short exact sequence of abelian groups
splits over the free group $\mathbf Z$, giving the direct-sum
decomposition.
