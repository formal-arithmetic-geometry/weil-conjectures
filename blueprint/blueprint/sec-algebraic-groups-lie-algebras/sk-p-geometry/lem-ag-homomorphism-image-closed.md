+++
id = "lem-ag-homomorphism-image-closed"
kind = "lemma"
title = "The image of a regular homomorphism is closed"
order = 2495
uses = ["def-wf-algebraic-components", "lem-wf-affine-constructible-open", "lem-wf-algebraic-component-cosets"]
+++
Let $G\subseteq\operatorname{GL}(V)$ and $K\subseteq\operatorname{GL}(W)$
be closed reduced matrix groups over $k=\overline{\mathbf Q}_\ell$, and
let $\varphi:G\to K$ be a regular homomorphism, that is, a morphism of
varieties which is a group homomorphism on $k$-points. Then the image
$S=\varphi(G(k))$ is a closed subgroup of $K(k)$: it is the set of
$k$-points of a closed subgroup of $K$, which we equip with its reduced
structure.

## Proof

Since $\varphi$ is a homomorphism, $S$ is a subgroup of $K(k)$. For any
subgroup $H\subseteq K(k)$ its Zariski closure $\overline H$ is again a
subgroup: for fixed $y\in H$ the closed condition $xy\in\overline H$
holds on $H$, hence on $\overline H$; then for fixed $x\in\overline H$
the closed condition $xy\in\overline H$ holds on $H$, hence on
$\overline H$; inversion is the same argument.

First treat the identity component. By
[lem-wf-algebraic-component-cosets], $G^\circ$ is an irreducible closed
subset of the affine variety $\operatorname{GL}(V)$, hence an
irreducible affine variety. Put $S_0=\varphi(G^\circ(k))$, a subgroup of
$S$, and let $T=\overline{S_0}\subseteq K$ with its reduced structure.
Then $T$ is a closed subgroup; it is irreducible as the closure of the
image of an irreducible space, and it is affine, being closed in
$\operatorname{GL}(W)$. The morphism $\varphi|_{G^\circ}:G^\circ\to T$ is a
morphism of affine schemes of finite type over $k$, so by part (1) of
[lem-wf-affine-constructible-open] its image
$\varphi(G^\circ)\subseteq T$ is constructible. It is dense in $T$,
because its closed points $S_0$ are already dense; hence part (2)
of [lem-wf-affine-constructible-open] gives a nonempty open
$U\subseteq T$ contained in the image. On $k$-points: every closed
point $t\in U$ has a nonempty fibre, which is a nonempty finite-type
$k$-scheme and therefore has a $k$-point because $k$ is algebraically
closed; hence $U(k)\subseteq S_0$, and $U(k)\neq\varnothing$.

Now

$$
U(k)^{-1}U(k)=\bigcup_{u\in U(k)}u^{-1}U(k)
$$

is the set of $k$-points of an open neighbourhood of the identity in
$T$, and it lies in the subgroup $S_0$. Its translates $sU^{-1}U$ for
$s\in S_0$ show that $S_0$ is open in $T(k)$; the other cosets of $S_0$
in $T(k)$ are open for the same reason, so $S_0$ is also closed in
$T(k)$. Since $S_0$ is dense in $T$, we get $S_0=T(k)$. Thus
$\varphi(G^\circ(k))$ is the set of $k$-points of the closed subgroup
$T$.

Finally, by [lem-wf-algebraic-component-cosets] the group $G(k)$ is the
union of finitely many cosets $g_1G^\circ(k),\ldots,g_nG^\circ(k)$ (as
in [def-wf-algebraic-components], $G^\circ$ is the identity component).
Therefore

$$
S=\bigcup_{i=1}^n\varphi(g_i)\,T(k),
$$

a finite union of translates of the closed set $T(k)$. Each translate
is closed, so $S$ is the set of $k$-points of the closed reduced
subvariety $\bigcup_i\varphi(g_i)T$ of $K$, which is a subgroup because
$S$ is and closed subvarieties of $K$ are determined by their
$k$-points.
