+++
id = "thm-sc-theorem-of-the-base"
kind = "theorem"
title = "The theorem of the base"
order = 849
uses = ["def-pc-genus", "def-pc-geometrically-irreducible", "def-pc-smooth-projective-curve", "def-sc-picard-functor", "lem-sc-riemann-roch", "prop-pd-picard-degree-decomposition", "thm-pc-picard-representable"]
+++
Let $k$ be a separably closed field and let $C$ be a
smooth projective curve over $k$
which is geometrically integral,
of genus $g=g(C)=\dim_kH^1(C,\mathcal O_C)$ ([def-pc-genus]). Then the
Picard functor $\operatorname{Pic}_{C/k}$ of
[def-sc-picard-functor] is a disjoint union over $d\in\mathbf Z$ of smooth proper $g$-dimensional $k$-varieties
$\operatorname{Pic}^d_{C/k}$, whose $k$-points are the
degree-$d$ invertible modules, and
$\operatorname{Pic}^0_{C/k}$ is an open and closed subgroup
scheme; in particular $\operatorname{Pic}^0_{C/k}$ is a proper
smooth group scheme of dimension $g$.

## Proof

*Reference: Stacks Project, Picard Schemes of Curves, Lemma
44.6.7, [Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0).* The argument of loc. cit. is the following. By Derived
Categories of Schemes, Lemma 36.32.2,
[Tag 0B9T](https://stacks.math.columbia.edu/tag/0B9T), the
Picard functor decomposes as a disjoint union over $d\in\mathbf Z$ of open and closed subfunctors $\operatorname{Pic}^d_{C/k}$,
classified by the fibrewise Euler characteristic
$\chi(X_t,\mathcal L_t)=d+1-g$. Smoothness and dimension: the
Hilbert scheme $\underline{\mathrm{Hilb}}^g_{C/k}$ is smooth of
dimension $g$ (Proposition 44.3.6,
[Tag 0B9I](https://stacks.math.columbia.edu/tag/0B9I)); the
morphism $\gamma_g:\underline{\mathrm{Hilb}}^g\to \operatorname{Pic}^g$, $D\mapsto\mathcal O_C(D)$, is an open
immersion on a nonempty open (as the proof of representability of
[thm-pc-picard-representable] shows), and the translates of this open by $k$-points of the
group scheme form an open covering, so
$\operatorname{Pic}_{C/k}$ is smooth of dimension $g$.
Properness: for $d\geq g$ the map
$\gamma_d:\underline{\mathrm{Hilb}}^d_{C/k}\to\operatorname{Pic}^d$,
$D\mapsto\mathcal O_C(D)$, given by the universal divisor (Remark
44.3.7, [Tag 0B9J](https://stacks.math.columbia.edu/tag/0B9J)), is surjective: for $\mathcal L\in\operatorname{Pic}^d(K)$
one has $\chi(C_K,\mathcal L)=d+1-g>0$ ([lem-sc-riemann-roch]), so
$\mathcal L$ has a nonzero global section, which yields
$\mathcal L\cong\mathcal O_C(D)$ for an effective divisor $D$
of degree $d$. The Hilbert scheme is proper over $k$ (it is
projective), and the image of a proper scheme in a separated target
is proper (Morphisms of Schemes, Lemma 29.42.10,
[Tag 0AH6](https://stacks.math.columbia.edu/tag/0AH6)), so
$\operatorname{Pic}^d_{C/k}$ is proper for $d\geq g$; every
other component is isomorphic to one of these by a translation under
the group law ([prop-pd-picard-degree-decomposition](4): translation by
$\mathcal O_C(eP)$ maps $\operatorname{Pic}^d_{C/k}$ isomorphically onto
$\operatorname{Pic}^{d+e}_{C/k}$), hence proper. Therefore the open and closed subgroup scheme
$\operatorname{Pic}^0_{C/k}$ is proper and smooth of dimension
$g$.
