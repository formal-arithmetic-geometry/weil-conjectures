+++
id = "lem-exc-direct-image-coproducts"
kind = "lemma"
title = "Finite cohomological dimension gives derived coproduct compatibility"
order = 1561
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "lemma-weil-pbc-direct-image-filtered-colimit"]
+++
Let $u:U\to T$ be
quasi-compact and
quasi-separated, and let $A$ be a finite ring. Suppose that
$R^pu_*M=0$ for all etale $A$-module sheaves $M$ and
$p>c$, where $c\geq0$. Then
$Ru_*$ preserves arbitrary
coproducts on the unbounded
ordinary derived categories.

## Proof

A direct sum is the filtered colimit of its finite subsums.
Additivity and [lemma-weil-pbc-direct-image-filtered-colimit]
therefore show that every $R^pu_*$ commutes with direct sums of
sheaves. We explain why the sheaf assertion also gives the unbounded
derived assertion, which does not follow from additivity alone.

Use a functorial Godement resolution in the etale topos, and truncate
it after degree $c$, retaining the cokernel in that degree.
Godement terms are acyclic for direct image. Dimension shifting gives
$R^pu_*C^c(M)=R^{p+c}u_*M=0$ for $p>0$, so the last term is
also acyclic. The resolution functors and their successive cokernel
functors are exact. Applied degreewise to an arbitrary complex, this
finite-length resolution computes its derived direct image: resolving
again by injectives verifies the comparison, and the horizontal
resolution has only $c+1$ columns. Thus the hypercohomology
spectral sequence

$$
R^pu_*\mathcal H^q(K)\Longrightarrow
\mathcal H^{p+q}(Ru_*K),\qquad 0\leq p\leq c,
$$

has a finite filtration in each total degree, also for unbounded $K$.
This is a finite-width double-complex calculation in the ordinary
derived categories of [def-weil-pbc-derived-categories].

For a family $(K_s)$, coproducts of module sheaves are exact, so
$\mathcal H^q(\bigoplus_s K_s)=\bigoplus_s\mathcal H^q(K_s)$.
The canonical map $\bigoplus_s Ru_*K_s\to Ru_*(\bigoplus_s K_s)$
is an isomorphism on the displayed spectral-sequence entries by the
first paragraph. It is consequently an isomorphism on the abutment,
by induction along its finite filtration, in every degree. It is
therefore an isomorphism in the derived category.
