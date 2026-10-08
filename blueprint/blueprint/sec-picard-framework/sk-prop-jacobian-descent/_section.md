+++
id = "sk-prop-jacobian-descent"
kind = "section"
title = "The Jacobian over a general base field, by Galois descent"
order = 851
uses = ["sk-def-av-jacobian", "sk-def-av-pic", "sk-def-picard-pic", "sk-prop-av-projective", "sk-prop-jacobian", "sk-prop-picard-degree-decomposition", "sk-prop-picard-pic-split", "sk-thm-picard-main"]
lean = ["AlgebraicGeometry.exists_jacobian_descent"]
+++
*Proposition (sketch).*

Let $k_0$ be any field, $k_s$ a separable closure and $\bar k_0$ an
algebraic closure containing it, and let $C_0$ be a proper smooth
geometrically connected curve of genus $g$ over $k_0$; put
$C=C_0\times_{k_0}\bar k_0$. The Jacobian $J(C)$ and its representing
isomorphism in [sk-prop-jacobian] descend canonically to $k_0$,
compatibly with base change; write $J_0$ for this descended abelian
variety. The induced identification $J_0(\bar k_0)=\Pic^0(C)$ is
*equivariant* for the natural actions of
$\operatorname{Gal}(k_s/k_0)$: on the left through the $k_0$-structure of
$J_0$, on the right through that of $C_0$. In particular, for every $n$
and every $\ell$, restricting to $\ell^n$-torsion gives a
$\operatorname{Gal}(k_s/k_0)$-equivariant isomorphism
$J_0[\ell^n](\bar k_0)\cong\Pic^0(C)[\ell^n]$. No rational point of
$C_0$ is assumed; the finite-field case $k_0=\mathbf F_q$ is the one used
downstream.

## Proof

Write $C_s=C_0\times_{k_0}k_s$ and
$F:=\Pic^0_{C_0/k_0}\subseteq\Pic_{C_0/k_0}$ for the subsheaf of classes
of fibrewise degree $0$ ([sk-def-picard-pic]). The Picard functor
commutes with base change, so the restriction of $F$ to $(\Sch/k_s)$ is
$\Pic^0_{C_s/k_s}$ and its restriction to $(\Sch/\bar k_0)$ is
$\Pic^0_{C/\bar k_0}$.

*Step 1 (the geometric case, carried out over the separable
closure).* Over $\bar k_0$ the functor $\Pic^0_{C/\bar k_0}$ is
represented by the abelian variety $J(C)$ of dimension $g$, with
$J(C)(\bar k_0)=\Pic^0(C)$: this is [sk-prop-jacobian]. The
construction is available already over $k_s$: [sk-thm-picard-main]
is stated for a separably closed field, so $\Pic_{C_s/k_s}$ is
represented by a group scheme $P_s$ over $k_s$. The
degree-decomposition argument of [sk-prop-picard-degree-decomposition]
applies over $k_s$ (its inputs are the perfect complex of
[sk-thm-picard-semicon], Riemann–Roch with $H^0(C_s,\cO)=k_s$, which
holds because $C_s$ is smooth and geometrically connected, and a
$k_s$-point of $C_s$ from [sk-prop-picard-dense-points]), so the
degree-zero locus $J_s:=P_s^0$ is an open and closed subgroup scheme of
$P_s$ representing $\Pic^0_{C_s/k_s}$, and
$J_s\times_{k_s}\bar k_0\cong J(C)$ since both represent
$\Pic^0_{C/\bar k_0}$. Properness, smoothness, geometric connectedness
and the dimension descend along the faithfully flat $k_s\to\bar k_0$, so
$J_s$ is an abelian variety of dimension $g$ over $k_s$.

*Why a rational point over a finite extension is not enough.* One
cannot instead pass to a finite Galois extension $k_1/k_0$ over which
$C_0$ acquires a rational point and run the rigidified construction of
[sk-thm-picard-main] over $k_1$: that construction verifies the
criterion of [sk-thm-picard-criterion] with the twist lemma
[sk-thm-picard-twist], which needs the dense set of rational points of
a separably closed field. Over $\mathbf F_2$ the genus-$2$ curve
$y^2+y=x^5+x^3+1$ has a rational point $P$, but every degree-zero line
bundle on it is trivial (its only effective divisors of degree $2$ are
$2P$ and the fibres over $x=0$ and $x=1$, all linearly equivalent via
$x$ and $x+1$), so $\omega_C$ admits no twist $\omega_C\otimes\cL_0$ with
$h^0=1$ and $h^1=0$. Likewise, finitely many equations over $\bar k_0$
need not be defined over a separable extension of an imperfect $k_0$.
The spreading out below is therefore done from $k_s$, where Step 1 holds.

*Step 2 (the canonical descent datum and its finite level).*
Since $F$ is a functor on $(\Sch/k_0)$ and $J_s$ represents its
restriction to $(\Sch/k_s)$, the two pullbacks of $J_s$ to
$\Spec(k_s\otimes_{k_0}k_s)$ both represent the restriction of $F$
there; Yoneda gives a canonical isomorphism between them satisfying
the cocycle condition on the triple tensor product, i.e. a descent
datum on $J_s$ relative to $\Spec k_s\to\Spec k_0$, defined without
choosing a Galois action. Now $k_s=\bigcup k_1$ over the finite Galois
subextensions $k_1/k_0$, so $\Spec k_s=\varprojlim\Spec k_1$ with
affine transition maps. The abelian variety $J_s$ is projective
([sk-prop-av-projective]) and of finite presentation over $k_s$, and
the descent datum consists of finitely many morphisms and identities
between schemes of finite presentation; by finite-presentation descent
along the limit (Stacks
[01ZM](https://stacks.math.columbia.edu/tag/01ZM)) there
are a finite Galois extension $k_1/k_0$, a projective $k_1$-scheme
$J_1$ with $J_1\times_{k_1}k_s\cong J_s$, and a descent datum on $J_1$
relative to $k_1/k_0$ whose base change to $k_s$ is the canonical one.
Nothing is claimed at this point about $J_1$ representing $\Pic^0$ of
$C_0\times_{k_0}k_1$; that follows only in Step 4.

*Step 3 (effective descent).* $\Spec k_1\to\Spec k_0$ is finite
locally free and surjective and $J_1$ is projective, so the descent
datum is effective (Stacks
[0CCJ](https://stacks.math.columbia.edu/tag/0CCJ)): there
is a $k_0$-scheme $J_0$ with $J_0\times_{k_0}k_1\cong J_1$, hence
$J_0\times_{k_0}k_s\cong J_s$ compatibly with the canonical descent
datum, and $J_0\times_{k_0}\bar k_0\cong J(C)$. Properness, smoothness,
geometric connectedness and the dimension descend along the faithfully
flat $k_0\to k_s$. This is the step that dispenses with a rational
point of $C_0$.

*Step 4 (the representing isomorphism descends).* The sheaf $F$
is limit preserving: an invertible module on $C_0\times_{k_0}T$ for
$T=\varprojlim T_i$ ($T_i$ quasi-compact and quasi-separated, affine
transition maps) is pulled back from some $C_0\times_{k_0}T_i$, and two
such modules that become isomorphic on the limit do so at a finite
stage (EGA IV$_3$ 8.5.2), and fppf sheafification preserves this. Hence
for a $k_0$-scheme $T$, writing $T_{k_s}=\varprojlim_{k_1}T_{k_1}$,

$$
F(T)=\varinjlim_{k_1}\operatorname{Eq}\bigl(F(T_{k_1})\rightrightarrows
F(T_{k_1\otimes_{k_0}k_1})\bigr)
=\operatorname{Eq}\bigl(F(T_{k_s})\rightrightarrows
F(T_{k_s\otimes_{k_0}k_s})\bigr),
$$

the first equality being the fppf sheaf property for the covers
$T_{k_1}\to T$. The representable functor $h_{J_0}$ satisfies the same
equalizer formula, being an fpqc sheaf. The isomorphism
$h_{J_s}\cong F|_{(\Sch/k_s)}$ is compatible with the two descent data
(the datum on $J_s$ was defined from it), so it identifies the two
equalizers: $h_{J_0}\cong F$. Thus $J_0$ represents $\Pic^0_{C_0/k_0}$;
in particular it is a group scheme, hence an abelian variety of
dimension $g$ over $k_0$, and $J_0\times_{k_0}K$ represents
$\Pic^0_{C_K/K}$ for every field extension $K/k_0$ (base-change
compatibility of $F$). For $K=\bar k_0$ this recovers $J(C)$ with its
representing isomorphism, and
$J_0(\bar k_0)=F(\bar k_0)=\Pic^0(C)$ by [sk-prop-picard-pic-split]
(with $\Pic(\Spec\bar k_0)=0$).

*Step 5 (equivariance).* For
$\tau\in\operatorname{Gal}(k_s/k_0)$, extended uniquely to $\bar k_0$,
the automorphism $\Spec\tau$ of the $k_0$-scheme $\Spec\bar k_0$ induces
an endomorphism of $h_{J_0}(\bar k_0)$ (the action through the
$k_0$-structure of $J_0$) and of $F(\bar k_0)=\Pic^0(C)$ (pullback along
$\id_{C_0}\times\Spec\tau$, the action through the $k_0$-structure of
$C_0$). The isomorphism $h_{J_0}\cong F$ of Step 4 is a natural
transformation of functors on $(\Sch/k_0)$, so it commutes with both:
$J_0(\bar k_0)=\Pic^0(C)$ is $\operatorname{Gal}$-equivariant, and so is
its restriction to $\ell^n$-torsion.

The detailed form, stated over an arbitrary base field, is Blueprint 06b,
`thm-pd-jacobian-general-field` (Steps 1–4 are
`thm-pd-geometric-pic0`, `lem-pd-canonical-descent-datum`,
`cor-pd-finite-level` and `thm-pd-effective-descent`);
the rigidified construction over separably closed fields is Blueprint
50, `thm-pc-picard-representable` (Stacks
[0B9Z](https://stacks.math.columbia.edu/tag/0B9Z), which
keeps the separably closed hypothesis), and the passage from $k_s$ to a
general base is exactly Steps 2–4.

Uses: [sk-def-picard-pic], [sk-prop-av-projective], [sk-prop-jacobian], [sk-prop-picard-degree-decomposition], [sk-prop-picard-pic-split], [sk-thm-picard-main]
