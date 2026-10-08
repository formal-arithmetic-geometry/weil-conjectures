+++
id = "p-product"
kind = "theorem"
title = "The central--geometric product"
order = 2523
tags = ["latex:proposition"]
uses = ["d-monodromy", "lem-ag-closure-commutators", "lem-ag-closure-semisimple", "lem-ag-faithful-semisimple-lie-central-radical", "lem-ag-homomorphism-image-closed", "lem-ag-lie-centre", "lem-ag-lie-stable-subspace", "lem-wf-algebraic-component-cosets", "lem-wf-same-lie-closed-subgroup"]
lean = ["AlgebraicGeometry.GeneralLinearGroup.surjective_mulCenterIdentityComponent", "AlgebraicGeometry.GeneralLinearGroup.exists_mul_eq_of_containsCommutators", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.surjective_mul_center_geometricMonodromy", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.exists_mem_center_mul_mem_geometricMonodromy_eq"]
+++
For a semisimple represented degree datum ([d-monodromy]), the
identity components and center satisfy

$$
G^\circ=Z(G^\circ)^\circ H^\circ.
$$

This applies to the Weil representation of a lisse Weil sheaf whose Weil
representation is semisimple.

## Proof

Use the defining representation of [d-monodromy]. By
[lem-ag-closure-semisimple], $V$ is a semisimple $G^\circ$-module:
$V=\bigoplus_iM_i$ with each $M_i$ a simple $G^\circ$-module. Set
$\mathfrak g=\operatorname{Lie}(G^\circ)\subseteq\operatorname{End}(V)$,
$\mathfrak h=\operatorname{Lie}(H^\circ)$ and $T=Z(G^\circ)^\circ$.
Apply [lem-ag-lie-stable-subspace] to the connected group $G^\circ$ and
its inclusion $r:G^\circ\to\operatorname{GL}(V)$, whose differential is
the inclusion $dr:\mathfrak g\subseteq\operatorname{End}(V)$: a subspace
of $V$ is $G^\circ$-stable if and only if it is $\mathfrak g$-stable.
Hence each $M_i$ is $\mathfrak g$-stable, and its $\mathfrak g$-stable
subspaces are exactly its $G^\circ$-stable subspaces, so $M_i$ has no
$\mathfrak g$-stable subspaces other than $0$ and $M_i$. Thus the Lie
representation $\mathfrak g\subseteq\operatorname{End}(V)$ is semisimple,
and it is faithful because it is an inclusion. By
[lem-ag-faithful-semisimple-lie-central-radical],
$\mathfrak g=Z(\mathfrak g)+[\mathfrak g,\mathfrak g]$, and
[lem-ag-closure-commutators] and [lem-ag-lie-centre] give

$$
\mathfrak g=Z(\mathfrak g)+[\mathfrak g,\mathfrak g]
           =Z(\mathfrak g)+\mathfrak h
           =\operatorname{Lie}(T)+\operatorname{Lie}(H^\circ).
$$

Here the middle equality holds because
$[\mathfrak g,\mathfrak g]\subseteq\mathfrak h\subseteq\mathfrak g$.

The group $H^\circ$ is connected and contains $1$, and $H\subseteq G$, so
$H^\circ\subseteq G^\circ$ ([lem-wf-algebraic-component-cosets]); the
central subgroup $T$ of $G^\circ$ commutes with it. The product
$T\times H^\circ$, embedded block-diagonally in
$\operatorname{GL}(V\oplus V)$, is a closed matrix group, and the
multiplication map

$$
\mu:T\times H^\circ\to G^\circ,\qquad(t,h)\mapsto th,
$$

is a morphism of varieties and, since $T$ is central, a group
homomorphism: $tht'h'=tt'hh'$. By [lem-ag-homomorphism-image-closed] its
image $K=TH^\circ$ is a closed subgroup of $G^\circ$. It is connected:
$T$ and $H^\circ$ are connected and contain $1$, so both lie in the
identity component $K^\circ$ ([lem-wf-algebraic-component-cosets]),
and hence $K=TH^\circ\subseteq K^\circ$. Its Lie algebra is a subspace
containing $\operatorname{Lie}(T)$ and $\operatorname{Lie}(H^\circ)$,
hence equals $\mathfrak g$. Thus [lem-wf-same-lie-closed-subgroup]
gives $K=G^\circ$.
