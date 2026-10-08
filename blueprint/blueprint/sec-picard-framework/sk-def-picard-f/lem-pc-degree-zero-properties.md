+++
id = "lem-pc-degree-zero-properties"
kind = "lemma"
title = "Cohomology of a module in degree zero"
order = 820
uses = ["def-pc-derived-category", "def-pc-finite-locally-free", "def-sc-invertible-module"]
+++
Let $X$ be a scheme, $M\in D(\mathcal{O}_X)$ and let $\mathcal{N}$ be an
invertible $\mathcal{O}_X$-module with
$M\cong\mathcal{N}[0]$. Then $H^i(M)=0$ for $i\neq0$ and $H^0(M)\cong\mathcal{N}$. If
$M\cong E[-i]$ with $E$ locally free of rank $r$ (cf. [def-pc-finite-locally-free] and its [lem-pc-flf-properties]),
then $H^j(M)=0$ for $j\neq i$ and $H^i(M)\cong E$.

## Proof

By definition of the shift, $H^j(\mathcal{N}[0])$ is the $j$-th cohomology of
the complex with $\mathcal{N}$ in degree $0$, i.e. $0$ for $j e0$ and $H^0$ is
$\mathcal{N}$; cohomology is invariant under quasi-isomorphism, and
$M\cong\mathcal{N}[0]$ is an isomorphism in $D(\mathcal{O}_X)$, which means that the
two complexes are connected by a zig-zag of quasi-isomorphisms (that
each induces an isomorphism of all cohomology sheaves). The second
assertion is the same argument applied to the complex $E$ in degree
$-i$.
