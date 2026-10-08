+++
id = "lem-weil-pbc-hypercover-free-resolution"
kind = "lemma"
title = "The augmented free complex of a hypercover"
order = 948
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-finite-split-hypercover"]
+++
Let $U\to X$ be a split etale hypercover
[def-weil-pbc-finite-split-hypercover]. Write $\mathbb Z[V]$ for the
sheafification of the free abelian presheaf on the sheaf represented by an
etale $X$-scheme $V$. Then the alternating-face augmented complex

$$
 \cdots\longrightarrow\mathbb Z[U_2]\longrightarrow
 \mathbb Z[U_1]\longrightarrow\mathbb Z[U_0]
 \longrightarrow\mathbb Z[X]\longrightarrow0
$$

is exact. For an injective abelian sheaf $I$, its complex of sections
consequently satisfies $H^0(C^\bullet(U,I))=I(X)$ and
$H^p(C^\bullet(U,I))=0$ for $p>0$. The same assertions hold with free modules
over a constant ring.

## Proof

Exactness is a local assertion about the sheaves of
[def-weil-pbc-etale-sheaves]. A local chain has finite support. Choose
locally a vertex in $U_0$, using its covering of $X$. For each of the
finitely many simplices in a given chain, including its faces, construct a
cone to this vertex. Inductively, the cone on the boundary of a simplex has
already been specified. The matching-cover condition in
[def-weil-pbc-finite-split-hypercover] supplies a simplex with exactly those
faces after an etale cover. Take a common refinement for the finitely many
choices. Denote this cone operation by $h$. The alternating-face formula
gives $\partial h+h\partial=1$ on the augmented finite collection of chains:
the faces through the new vertex cancel and the remaining face is the
original simplex. Thus every cycle is locally a boundary. In degree zero the
same construction uses the augmentation, and proves its surjectivity as well.

The defining free-sheaf adjunction gives $\operatorname{Hom}(\mathbb
Z[V],I)=I(V)$. Applying $\operatorname{Hom}(-,I)$ to the exact augmented
complex is exact because $I$ is injective, which proves the assertions about
$C^\bullet(U,I)$. Replacing free abelian groups by free modules gives the
identical proof for a constant coefficient ring.
