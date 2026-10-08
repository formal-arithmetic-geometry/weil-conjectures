+++
id = "def-weil-poincare-trace-cup"
kind = "definition"
title = "Poincare trace and cup-product pairing"
order = 2421
uses = ["def-coefficient-twists-detailed", "def-compact-support-direct-image-detailed", "def-weil-derived-direct-image", "def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "def-weil-exceptional-adjoint-admissibility", "def-weil-exceptional-inverse-image", "def-weil-finite-field-fiber", "def-weil-geometric-hypotheses", "def-weil-ordinary-compact-cohomology"]
+++
Let $p$ be prime, let $a\in\mathbf Z_{\geq1}$, put $q=p^a$, and set
$k_0=\Fq$, and let $k=\Fbar$ be the fixed algebraic closure of $k_0$. Fix a
prime $\ell\neq p$, write $\Ql=\mathbf Q_\ell$, and choose an algebraic
closure $\Qlb$ of $\Ql$. Let $X_0/k_0$ be smooth, proper, and geometrically
connected of pure dimension $d\in\mathbf Z_{\geq0}$. Put
$X=X_0\times_{k_0}k$, and let $a_X:X\to\Spec k$ be its structure morphism.
Write $H^i(X,-)$ and $H_c^i(X,-)$ for the ordinary and compactly supported
cohomology groups, and, for every integer $m$, write $\Ql(m)$ for the Tate
twist [def-coefficient-twists-detailed] of degree $m$. Write $Ra_X^!$ for
the constructible exceptional inverse image of
[def-weil-exceptional-inverse-image] at $\Ql$ and $\Qlb$ — defined for every
separated finite-type morphism, so no admissibility hypothesis on $a_X$ is
imposed (the ambient notion of [def-weil-exceptional-adjoint-admissibility]
is not used) — and $\otimes^L$ for the derived tensor product, using the
derived pullback/tensor/Hom notation. Choose an
orientation isomorphism for the smooth structure morphism $a_X:X\to\Spec k$,

$$
 \eta_X:Ra_X^!\Ql\xrightarrow{\sim}(\Ql)_X(d)[2d],
$$

where $\Ql(d)$ uses the Tate twist [def-coefficient-twists-detailed] of degree $d$. We
use $Ra_{X*}$ and $Ra_{X!}$ for the derived direct image and the
compact-support direct image [def-compact-support-direct-image-detailed],
respectively. Through $\eta_X$, the counit $Ra_{X!}Ra_X^!\Ql\to\Ql$ defines
the trace map

$$
 \operatorname{tr}_X:H_c^{2d}(X,\Ql(d))\longrightarrow\Ql.
$$

For the proper structure morphism, use the compact-support direct image
[def-compact-support-direct-image-detailed] comparison and, after untwisting, write

$$
 \operatorname{tr}^{(-d)}_X:H^{2d}(X,\Ql)\longrightarrow\Ql(-d).
$$

The multiplication $(\Ql)_X\otimes^L(\Ql)_X\to(\Ql)_X$ defines, for all
integers $i,j$, cup products

$$
\smile:H^i(X,\Ql)\otimes_{\Ql}H^j(X,\Ql)
 \longrightarrow H^{i+j}(X,\Ql).
$$

For $x\in H^i(X,\Ql)$ and $y\in H^j(X,\Ql)$, the cup product is
graded-commutative:

$$
 y\smile x=(-1)^{ij}x\smile y
 \qquad
 (x\in H^i(X,\Ql),\ y\in H^j(X,\Ql)).
$$

For every integer $i$ with $0\leq i\leq2d$, and for every $x\in H^i(X,\Ql)$
and $y\in H^{2d-i}(X,\Ql)$, define

$$
 \langle x,y\rangle_i=
 \operatorname{tr}^{(-d)}_X(x\smile y):
 H^i(X,\Ql)\times H^{2d-i}(X,\Ql)
 \longrightarrow\Ql(-d).
$$
