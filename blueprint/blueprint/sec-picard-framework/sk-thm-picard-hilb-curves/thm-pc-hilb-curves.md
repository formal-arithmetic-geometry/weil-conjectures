+++
id = "thm-pc-hilb-curves"
kind = "theorem"
title = "Hilbert schemes of smooth projective curves"
order = 790
uses = ["def-pc-base-change", "def-pc-curve", "def-pc-degree-line-bundle", "def-pc-hilb-functor", "def-pc-morphism-conventions", "def-sc-effective-cartier-divisor", "lem-pc-ample-positive-degree", "lem-pc-cartier-criterion", "lem-pc-degree-base-change", "lem-pc-flat-source-descent", "lem-pc-hilb-addition", "lem-pc-hilb-representable", "lem-pc-hilb-smooth", "lem-sc-ample-complement-affine", "thm-pqf-finite-iff-proper-finite-fibres"]
lean = ["AlgebraicGeometry.hilbertPresheaf_curve_representable", "AlgebraicGeometry.hilbertPresheaf_curve_points", "AlgebraicGeometry.hilbertPresheaf_curve_add"]
+++
(Picard Schemes of Curves, Proposition 44.3.6, Tag
[0B9I](https://stacks.math.columbia.edu/tag/0B9I).) Let $X$ be a
geometrically irreducible smooth proper curve over a field $k$ and let
$d\geq0$. Then:

1. $\operatorname{Hilb}^d_{X/k}$ is representable by a smooth proper variety
$\underline{\operatorname{Hilb}}^d_{X/k}$ of dimension $d$ over $k$;
1. for a field extension $k'/k$ the $k'$-rational points of
$\underline{\operatorname{Hilb}}^d_{X/k}$ are in bijection with the effective Cartier
divisors of degree $d$ on $X_{k'}$;
1. for $d_1,d_2\geq0$ there is a morphism
$$
\underline{\operatorname{Hilb}}^{d_1}_{X/k}\times_k\underline{\operatorname{Hilb}}^{d_2}_{X/k}
\longrightarrow\underline{\operatorname{Hilb}}^{d_1+d_2}_{X/k}
$$
which is finite locally free of degree $\binom{d_1+d_2}{d_1}$.

## Proof

*Step 0: the affine-open hypothesis.*
We verify the hypotheses of [lem-pc-hilb-representable]: $X$ is proper,
hence separated, over $k$, and it remains to check the affine-open condition.
Given finitely many points $x_1,\ldots,x_d\in X$, choose a closed
point $Q$ different from every closed point in this list.
Such a $Q$ exists: the complement of finitely many closed points
is a nonempty open of the one-dimensional integral variety $X$;
a nonempty affine open inside it has a maximal ideal with residue
field finite over $k$ by Zariski's lemma. This point is closed in
$X$, since its residue field is finite over $k$.
The divisor $[Q]$ is effective Cartier on the smooth curve and
has positive degree $[\kappa(Q):k]$ by
[lem-pc-degree-base-change]. Therefore $\mathcal O_X(Q)$ is
ample by [lem-pc-ample-positive-degree], and
$X\setminus\{Q\}$ is affine by [lem-sc-ample-complement-affine].
It contains all the prescribed points, including the generic
point. This proves the affine-open hypothesis.

*Step 1: representability and the properties (1).* By
[lem-pc-hilb-representable] the functors
$\operatorname{Hilb}^d_{X/k}$ are representable by schemes $H_d:=\underline{\operatorname{Hilb}}^d_{X/k}$
for all $d\ge0$. The scheme $H_d$ is smooth of relative dimension $d$
over $k$ by [lem-pc-hilb-smooth]. It is separated over $k$: the
diagonal $\Delta:H_d\to H_d\times_kH_d$ is a closed immersion: let
$Z_1,Z_2\in\operatorname{Hilb}^d_{X/k}(H_d\times_kH_d)$ be the two pullbacks of the
universal object along the projections; a morphism $T\to H_d\times_kH_d$ factors through $\Delta$ iff $Z_{1,T}=Z_{2,T}$ (the
universal property: a $T$-valued point of $H_d\times H_d$ is a pair
of elements of $\operatorname{Hilb}^d(T)$; they are equal iff the pair comes from
$H_d$ via the diagonal); the locus $\{\,T:\ Z_{1,T}=Z_{2,T}\,\}$ is
closed in $H_d\times H_d$: it is the intersection of the closed loci
$\{Z_1\subseteq Z_2\}$ and $\{Z_2\subseteq Z_1\}$, each of which is
closed by the closed-immersion claim of the proof of
[lem-pc-hilb-representable] (Step 1 there: applied with
$Y=X_{H\times H}$, $X'=Z_1$ (closed in $X_{H\times H}$— yes: $Z_1$
is closed in $X_{H_d\times_kH_d}$) and $Z=Z_2$ – the locus where
$Z_{2,T}\subseteq Z_{1,T}$ is closed). Hence $\Delta$ is a closed
immersion, i.e. $H_d$ is separated over $k$ (the standard
characterization of separatedness via the diagonal,
[def-pc-morphism-conventions]). It is proper: by
[lem-pc-hilb-addition] the morphism
$H_{d-1}\times_kX\to H_d$ is finite locally free of degree $d$; the
iterated composite

$$
\pi_d:X^d=X\times_k\cdots\times_kX\;\longrightarrow\;H_d,
\qquad
(x_1,\dots,x_d)\longmapsto x_1+\cdots+x_d
$$

(the addition applied successively) is finite locally free of degree
$d!$ (composites of finite locally free morphisms of degrees
$1,2,\dots,d$: the degree multiplies, the classical multiplicativity:
the composite $H_{d-1}\times X\to H_d$ has degree $d$; the
projection $X^d\to X^{d-1}\times X$ is an isomorphism
($X^d\cong X^{d-1}\times X$), the composite
$X^d\to H_{d-1}\times X$ (the product of $\pi_{d-1}$ with
$\mathrm{id}_X$) has degree $(d-1)!$ by the multiplicativity of the
degree (the degree of a product of finite locally free morphisms is
the product of the degrees: the rank of the finite locally free
module attached to the fibre product is the tensor product of the
modules, whose rank multiplies), and the composite of $X^d\to H_{d-1}\times X$ with $H_{d-1}\times X\to H_d$ has degree
$(d-1)!\cdot d=d!$, the degree of a composite of finite locally free
morphisms being the product of the degrees (again multiplicativity,
or: the fibre of the composite over a point is the scheme of the
tensor product of the two finite locally free algebras, whose rank is
the product of the ranks). The morphism $\pi_d$ is
*surjective*: the image $I:=\pi_d(X^d)$ is closed
($X^d$ is proper, $\pi_d$ is finite hence proper, and the image of a
proper morphism is closed: the standard statement); for a closed
point $\bar t$ of $H_d\otimes_k\bar k$ the corresponding closed
subscheme $D_{\bar t}\subseteq X_{\bar k}$ is finite flat of rank
$d$ over $\bar k$, so it is a sum
$D_{\bar t}=y_1+\cdots+y_d$ of $\bar k$-points (with the
multiplicities $m_j$, $\sum_jm_j=d$: a finite flat scheme over an
algebraically closed field is a union of closed points with
Artinian structures), hence $\bar t$ lies in the image of
$X^d\otimes_k\bar k\to H_d\otimes_k\bar k$; so
$I\otimes_k\bar k$ contains every closed point of the scheme of
finite type $H_d\otimes_k\bar k$; since
$I\otimes_k\bar k$ is closed and the closed points of a scheme of
finite type over an algebraically closed field are dense,
$I\otimes_k\bar k=H_d\otimes_k\bar k$; as
$\bar k/k$ is faithfully flat, the closed subset $I$ has
$I\otimes_k\bar k=$ everything, hence $I=H_d$ (for a closed subset
$I$ with $I\otimes_k\bar k=H_d\otimes_k\bar k$: the closure
condition: if $x\in H_d\setminus I$ then the image point
$x_{\bar k}$ lies in $H_d\otimes\bar k\setminus I\otimes\bar k$,
contradiction). So $\pi_d$ is surjective.
Then $H_d$ is proper: $X^d$ is proper (finite products of proper schemes over $k$ are proper, the standard statement; and $X\to\operatorname{Spec} k$ is proper by hypothesis), $\pi_d$ is finite hence proper, so
$H_d=\pi_d(X^d)$ is the image of a proper scheme under a proper morphism, hence proper (Morphisms, Lemma 29.42.9, Tag
[03GN](https://stacks.math.columbia.edu/tag/03GN): the image of a proper morphism is proper). Finally $H_d$ is irreducible: $X^d$ is irreducible (geometrically irreducible over $k$: products of geometrically irreducible schemes over $k$ are irreducible: Varieties, Lemma 33.8.4, Tag
[038F](https://stacks.math.columbia.edu/tag/038F)), and the image of an irreducible scheme under a continuous surjective map is irreducible; together with smoothness (hence reducedness: smooth over the field $k$ is reduced, the standard statement) $H_d$ is an integral separated scheme of finite type over $k$ of dimension $d$, i.e. a variety over $k$ ([def-pc-curve]: a variety is an integral separated scheme of finite type over $k$). This proves (1).

*Step 2: the points of $H_d$; part (2).* For a field extension
$k'/k$: a $k'$-rational point of $H_d$ is, by the representability of
[def-pc-hilb-functor], the same as an element
$Z\in\operatorname{Hilb}^d_{X/k}(k')$, i.e. a closed subscheme
$Z\subset X_{k'}=X\times_{\operatorname{Spec} k}\operatorname{Spec} k'$ ([def-pc-base-change])
finite locally free of degree $d$ over $k'$. Since $X_{k'}\to k'$ is
smooth of relative dimension $1$ (base change of smooth), the
criteria of [lem-pc-cartier-criterion] apply with
$S=\operatorname{Spec}(k')$ and give: $Z\to k'$ is finite locally free
(i.e. (1)) iff $Z$ is a relative effective Cartier divisor on
$X_{k'}/k'$, iff $Z$ is an effective Cartier divisor on $X_{k'}$
(the relative condition being automatic over a field:
$Z\to k'$ is flat): i.e. the $k'$-points of $H_d$ are exactly the
effective Cartier divisors $D\subseteq X_{k'}$; its degree: the
effective Cartier divisor $D$ has degree $\deg(\mathcal{O}_{X_{k'}}(D))$
([def-pc-degree-line-bundle] and the divisor-degree formulas of
[lem-pc-degree-base-change](2)) and this equals the rank $d$ of
the finite locally free $Z\to k'$ (the classical: the degree of the
divisor is the length of $\mathcal{O}_D$, i.e. the rank over the field: the
computation of [lem-pc-degree-base-change](2): the fibre is
finite flat of rank $d$ over $k'$; and $\deg D=d$ iff the point has
degree $d$). This gives the bijection of (2).

*Step 3: the addition morphism; part (3).* For $d_1,d_2\ge0$ and
$T$ over $k$: an element of
$\operatorname{Hilb}^{d_1}_{X/k}(T)\times\operatorname{Hilb}^{d_2}_{X/k}(T)$ is a pair of closed
subschemes $D_1,D_2\subseteq X_T$ finite locally free of degrees
$d_1,d_2$ over $T$; by [lem-pc-cartier-criterion]
((1)$\Rightarrow$(2)) both are relative effective Cartier
divisors on $X_T/T$; the sum $D_1+D_2$ (the closed subscheme defined
locally by the product of the two defining equations: an effective
Cartier divisor, and flat over $T$: the short exact sequence
$0\to\mathcal{O}_{X_T}/(f_1)\to\mathcal{O}_{X_T}/(f_1f_2)\to\mathcal{O}_{X_T}/(f_2)\to0$
(exact because $f_1$ is a nonzerodivisor; the two ends flat over $T$)
shows $\mathcal{O}_{D_1+D_2}$ flat over $T$, and the rank is the sum
$d_1+d_2$) is again finite locally free of degree $d_1+d_2$ over
$T$: it is an element of $\operatorname{Hilb}^{d_1+d_2}_{X/k}(T)$. The assignment
$(D_1,D_2)\mapsto D_1+D_2$ is natural in $T$, so by the
representability of $\operatorname{Hilb}^{d_1+d_2}$ it is induced by a morphism

$$
\alpha:H_{d_1}\times_kH_{d_2}\longrightarrow H_{d_1+d_2} .
$$

The map $\alpha$ is proper, since its source is proper over $k$
and its target is separated over $k$, by part (1).
The surjection $u:=\pi_{d_1}\times\pi_{d_2}$ from
$X^{d_1+d_2}$ onto its source is finite locally free, and
$\alpha\circ u=\pi_{d_1+d_2}$ is finite locally free as well.
For every point of the target, the fibre of $\alpha$ is therefore
the surjective image of the finite fibre of $\pi_{d_1+d_2}$, so it
has finitely many points. Thus $\alpha$ is finite by
[thm-pqf-finite-iff-proper-finite-fibres].
It is flat by [lem-pc-flat-source-descent], since $u$ is a flat
surjection and the composite is flat. These are morphisms of
finite type schemes over a field, hence of finite presentation;
so $\alpha$ is finite locally free. We may now compute its rank
using the commutative diagram

$$
\begin{array}{ccc}
X^{d_1}\times_kX^{d_2}&\stackrel{\sim}{\longrightarrow}&X^{d_1+d_2}\\
\downarrow&&\downarrow\\
H_{d_1}\times_kH_{d_2}&\longrightarrow&H_{d_1+d_2}
\end{array}
$$

(the vertical left arrow is $\pi_{d_1}\times\pi_{d_2}$, the vertical
right $\pi_{d_1+d_2}$; the diagram commutes by the definition of $\alpha$
and the additivity of the sums). The left vertical arrow is finite
locally free of degree $d_1!\cdot d_2!$ (the degrees multiply), the
right vertical arrow of degree $(d_1+d_2)!$; with
$\deg(\alpha)=N$ the commutativity gives
$d_1!\,d_2!\,N=(d_1+d_2)!$ (the classical multiplicativity of the
degree of composites of finite locally free morphisms: the composite
has degree the product; the identity in the diagram is the identity of
the two schemes), so $N=\binom{d_1+d_2}{d_1}$. This proves (3).
