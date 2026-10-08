+++
id = "cor-galois-lisse-representations"
kind = "theorem"
title = "Lisse sheaves and continuous representations"
order = 2427
uses = ["def-galois-fibre-functor", "def-weil-pbc-constructible-complexes", "thm-galois-fundamental", "thm-galois-lc-etale"]
tags = ["latex:corollary"]
+++
Let $Y$ be connected with geometric point $\bar y$, and let $\Lambda$ be
a finite ring. Then evaluation at $\bar y$ is an exact equivalence between
locally constant sheaves of finite $\Lambda$-modules on $Y_{\Et}$ and
continuous $\Lambda$-linear representations of $\pi_1(Y,\bar y)$ on
finite $\Lambda$-modules. It is a tensor equivalence: for commutative
$\Lambda$ it carries $\mathcal F\otimes_\Lambda\mathcal G$ to
$\mathcal F_{\bar y}\otimes_\Lambda\mathcal G_{\bar y}$ with the diagonal
action and the constant sheaf $\Lambda$ to the trivial representation
$\Lambda$. It is compatible with base change along a map
$\Lambda\to\Lambda'$ of finite rings: it carries
$\Lambda'\otimes_\Lambda\mathcal F$ to
$\Lambda'\otimes_\Lambda\mathcal F_{\bar y}$ with the induced action. For $\Lambda=\overline{\mathbf Q}_\ell$ the
same holds for lisse $\overline{\mathbf Q}_\ell$-sheaves with finite
stalks, by the coefficient conventions of
[def-weil-pbc-constructible-complexes].

## Proof

Here $\pi_1=\pi_1(Y,\bar y)=\operatorname{Aut}(F_{\bar y})$ is the group
of [def-galois-fibre-functor]. A locally constant sheaf of finite
$\Lambda$-modules is, by
[thm-galois-lc-etale] applied to the underlying sheaf of sets together
with the module structure, a finite etale cover with a $\Lambda$-linear
action of its automorphism group; by [thm-galois-fundamental] such
objects correspond to finite continuous $\pi_1$-sets with $\Lambda$-linear
action, i.e. to continuous representations on finite $\Lambda$-modules.
The $\overline{\mathbf Q}_\ell$-statement follows by writing a lisse sheaf
with finite stalks as a filtered colimit of finite-level ones over the
coefficient stages of [def-weil-pbc-constructible-complexes].

*Exactness.* Let $u:\mathcal F\to\mathcal G$ be a map of locally
constant sheaves of finite $\Lambda$-modules. Choose an etale covering
$\{U_i\to Y\}$ on which both are constant, $\mathcal F|_{U_i}\cong
\underline M_i$ and $\mathcal G|_{U_i}\cong\underline N_i$. A map
$\underline M_i\to\underline N_i$ on $U_i$ is a locally constant function
$U_i\to\operatorname{Hom}_\Lambda(M_i,N_i)$, a finite set, so $U_i$ is a
finite disjoint union of open and closed pieces on each of which $u$ is
a constant map $M_i\to N_i$. Refining the covering by these pieces, the
kernel and cokernel of $u$ (taken in all sheaves of $\Lambda$-modules)
are constant on each piece with finite values, hence locally constant of
finite $\Lambda$-modules. So the locally constant sheaves form a full
abelian subcategory closed under kernels and cokernels, and the stalk
functor, being exact on all sheaves, is exact on it. On the
representation side kernels and cokernels are computed on the underlying
modules with the induced action, so evaluation at $\bar y$ is an exact
equivalence of abelian categories.

*Naturality of the action.* By [def-galois-fibre-functor] an element
$\sigma\in\pi_1$ is a natural automorphism of $F_{\bar y}$ on finite
locally constant sheaves of sets, so for every map
$\phi:\mathcal A\to\mathcal B$ of such sheaves
$\phi_{\bar y}\circ\sigma=\sigma\circ\phi_{\bar y}$; applied to the
two projections of $\mathcal A\times\mathcal B$ this shows that $\sigma$
acts diagonally on $(\mathcal A\times\mathcal B)_{\bar y}
=\mathcal A_{\bar y}\times\mathcal B_{\bar y}$.

*Tensor products.* Let $\Lambda$ be commutative. The sheaf
$\mathcal F\otimes_\Lambda\mathcal G$ (sheafified presheaf tensor product)
has stalk $\mathcal F_{\bar y}\otimes_\Lambda\mathcal G_{\bar y}$, and on a
common trivializing covering it is constant with finite value
$M_i\otimes_\Lambda N_i$, so it is locally constant of finite
$\Lambda$-modules. The canonical bilinear map
$\mathcal F\times\mathcal G\to\mathcal F\otimes_\Lambda\mathcal G$ is a
map of finite locally constant sheaves of sets, so by the previous
paragraph its stalk $\mathcal F_{\bar y}\times\mathcal G_{\bar y}\to
(\mathcal F\otimes_\Lambda\mathcal G)_{\bar y}$ is equivariant for the
diagonal action; hence the stalk isomorphism
$\mathcal F_{\bar y}\otimes_\Lambda\mathcal G_{\bar y}\cong
(\mathcal F\otimes_\Lambda\mathcal G)_{\bar y}$ is $\pi_1$-equivariant
for the diagonal action on the source. These isomorphisms are natural and
compatible with the associativity, commutativity and unit constraints,
since they are so on stalks. The constant sheaf $\underline\Lambda$ has a
section over $Y$ through every point of its stalk, and $\sigma$ fixes the
stalk of a global section (naturality applied to the map
$\underline{\{*\}}\to\underline\Lambda$), so it goes to the trivial
representation $\Lambda$.

*Base change of coefficients.* For $\Lambda\to\Lambda'$ a map of finite
rings, $\Lambda'\otimes_\Lambda\mathcal F$ has stalk
$\Lambda'\otimes_\Lambda\mathcal F_{\bar y}$, which is finite, and is
constant with value $\Lambda'\otimes_\Lambda M_i$ on each $U_i$, hence
locally constant of finite $\Lambda'$-modules. For each $\lambda'\in\Lambda'$
the map $\mathcal F\to\Lambda'\otimes_\Lambda\mathcal F$,
$s\mapsto\lambda'\otimes s$, is a map of finite locally constant sheaves of
sets, so its stalk commutes with every $\sigma$; since the elements
$\lambda'\otimes m$ generate $\Lambda'\otimes_\Lambda\mathcal F_{\bar y}$
additively, $\sigma$ acts on this stalk by $\lambda'\otimes m\mapsto
\lambda'\otimes\sigma m$, the induced action. The isomorphism is natural
in $\mathcal F$ and, for $\Lambda\to\Lambda'\to\Lambda''$, compatible with
composition, so evaluation at $\bar y$ commutes with base change of
coefficients (and, trivially, with restriction of scalars along
$\Lambda\to\Lambda'$).
