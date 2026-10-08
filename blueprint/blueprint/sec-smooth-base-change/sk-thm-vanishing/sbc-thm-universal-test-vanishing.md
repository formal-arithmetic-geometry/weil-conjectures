+++
id = "sbc-thm-universal-test-vanishing"
kind = "theorem"
title = "Vanishing in the universal curve test"
order = 1413
uses = ["def-sbc-normal-dominant-galois", "def-sbc-smooth-morphisms", "def-weil-pbc-scheme-conventions", "sbc-def-base-change-square", "sbc-lem-etale-over-normal", "sbc-lem-higher-direct-image-presheaf", "sbc-lem-slicing", "sbc-prop-torsors-h1", "sbc-thm-algebraically-closed-invariance", "sbc-thm-cohomological-dimension-of-an-affine-curve", "sbc-thm-spreading-finite-etale-galois"]
+++
Let

$$
\begin{array}{ccc}
X & \xleftarrow{\;h\;} & Y\\
f\big\downarrow & & \big\downarrow e\\
S & \xleftarrow{\;g\;} & \operatorname{Spec}K
\end{array}
$$

be a base-change square where
$X\to S$ is an affine smooth morphism of relative dimension one (in
the sense of [def-sbc-smooth-morphisms]) and $X$ is affine, $S$ is
the spectrum of a
normal domain $A$ with
algebraically closed fraction
field $L$, and $K/L$ is an extension of algebraically closed fields.
Let $d$ be an integer invertible on $S$. Then

$$
R^qh_*(\mathbf Z/d\mathbf Z)=0\qquad(q\geq1).
$$

## Proof

By [sbc-lem-higher-direct-image-presheaf] the sheaf
$R^qh_*\mathbf Z/d\mathbf Z$ is associated with

$$
U\longmapsto H^q\bigl(U\times_X Y,\mathbf Z/d\mathbf Z\bigr)
=H^q\bigl(U\times_S\operatorname{Spec}K,\mathbf Z/d\mathbf Z\bigr)
$$

on $X_{\Et}$. The remaining assertion is: given an affine $U\to X$ etale
and $\xi\in H^q(U\times_S\operatorname{Spec}K,\mathbf Z/d\mathbf Z)$,
there is an etale covering $\{U_i\to U\}$ such that $\xi$ dies in
$H^q(U_i\times_S\operatorname{Spec}K,\mathbf Z/d\mathbf Z)$.

For $q>1$: $U\times_S\operatorname{Spec}K$ is a smooth affine curve
over the algebraically closed field $K$ (it is affine, of finite type,
smooth and of dimension one), so the group vanishes by
[sbc-thm-cohomological-dimension-of-an-affine-curve] applied over $K$.

It remains to treat $q=1$. By [sbc-lem-slicing] we may replace $U$
by the members of an etale covering such that $U\to S$ factors as
$U\to V\to S$ with $U\to V$ affine smooth, with
geometrically connected
fibres in the sense of [def-sbc-normal-dominant-galois] and
a section $\sigma:V\to U$, and $V\to S$ etale; by
[sbc-lem-etale-over-normal] (the scheme $S$ is integral
normal in the sense of [def-sbc-normal-dominant-galois] with
algebraically closed, hence separably closed, function field $L$) the
separated etale $V\to S$ is a finite disjoint union of open
subschemes of $S$; replacing $S$ by one of these opens and $U$ by the
corresponding component does not change the fraction field $L$ of $S$,
so we may assume $X=U$ and $X\to S$ is affine smooth of relative
dimension one with geometrically connected fibres and a section
$\sigma:S\to X$, and $\xi\in H^1(Y,\mathbf Z/d\mathbf Z)$ with
$Y=X\times_S\operatorname{Spec}K$.

By [sbc-thm-algebraically-closed-invariance] applied to the
smooth separated curve $X_L=X\times_S\operatorname{Spec}L$ over $L$
and the extension $L\subseteq K$,

$$
H^1(X_L,\mathbf Z/d\mathbf Z)\xrightarrow{\ \sim\ }H^1(Y,\mathbf Z/d\mathbf Z),
$$

so $\xi$ corresponds to a class $\bar\xi$ on $X_L$. By
[sbc-prop-torsors-h1] and the finite-etale correspondence, $\bar\xi$
corresponds to a $\mathbf Z/d\mathbf Z$-torsor $P\to X_L$; the torsor
$P$ is a finite etale Galois cover of $X_L$ with group $\mathbf Z/d\mathbf Z$.
Over the $L$-rational point $\sigma(\eta)$ (the generic point
$\eta$ of $S$ has $\kappa(\eta)=L$), the restriction
$P_{\sigma(\eta)}$ is a $\mathbf Z/d\mathbf Z$-torsor over
$\operatorname{Spec}L$; since $L$ is algebraically closed
$H^1(\operatorname{Spec}L,\mathbf Z/d\mathbf Z)=0$, so this torsor is
trivial and $P$ has an $L$-point above $\sigma(\eta)$. The spreading
theorem [sbc-thm-spreading-finite-etale-galois] (with
$C=X$, $G=\mathbf Z/d\mathbf Z$, whose order $d$ is invertible on $S$)
gives a finite etale Galois cover $X'\to X$ with group
$\mathbf Z/d\mathbf Z$ whose restriction to $X_L$ is $P$. Then
$X'\times_XY=X'\times_{X_L}Y$ is the pullback of the torsor $P$ along
$P$ itself, hence has the diagonal section; the class of $\xi$ in
$H^1(X'\times_XY,\mathbf Z/d\mathbf Z)$ is the pullback of its
torsor-class, hence is zero: $\{X'\to X\}$ is the required etale
covering, and the associated sheaf is zero.
