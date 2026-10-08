+++
id = "def-weil-boundary-duality-input"
kind = "definition"
title = "The finite-stage boundary duality input"
order = 2129
uses = ["def-weil-exceptional-inverse-image", "def-weil-finite-torsion-constructibility", "lem-weil-closed-costalk-duality", "lem-weil-duality-pairing"]
+++
Fix $A=A_{E,n}$ and a separated finite-type $k$-scheme $Y$, where
$k=\overline{\mathbf F}_q$. The *boundary duality input* for
$(Y,A)$ consists of the following assertions, on the chosen finite-stage
coefficient categories.

1. For every locally closed $T\subseteq Y$, the exceptional
adjoints and their composition laws define
$\omega_T=Ra_T^!A$ and
$D_T=R\mathcal Hom_T(-,\omega_T)$, and $D_T$ carries
$D^b_{ctf}(T,A)$ into itself.
1. For every closed immersion $i:Z\hookrightarrow T$ between such
pieces, the canonical boundary exchange
$$
\beta_L:i^*D_TL\longrightarrow D_ZRi^!L
\qquad(L\in D^b_{ctf}(T,A))
$$
is an isomorphism. It is the adjoint of the pairing
$$
i^*D_TL\otimes^L Ri^!L\longrightarrow
Ri^!(D_TL\otimes^L L)\longrightarrow Ri^!\omega_T=\omega_Z.
$$
These comparisons are compatible with evaluation: using $\beta_{D_TK}$
and the inverse of $D_Z\alpha_K$ from
[lem-weil-closed-costalk-duality], the restriction $i^*\delta_K$
identifies with $\delta_{i^*K}$.

The first clause includes preservation as a separate condition. The second
clause interchanges ordinary and exceptional restriction; it does not
identify $i^*$ with $Ri^!$.
