+++
id = "lemma-weil-pbc-smooth-curve-kummer-localization"
kind = "lemma"
title = "Smooth prime-to-characteristic curve calculation"
order = 1146
uses = ["def-br", "def-weil-pbc-eight-curve-assertions"]
+++
Let $k$ be algebraically closed, let $C$ be a smooth separated finite-type
scheme of dimension at most one, and let
$\ell\ne\operatorname{char}k$. All eight applicable assertions
$\mathcal C_r(C,\underline{\mathbf F_\ell})$ hold, and every field-extension
map and open-restriction map is the one induced by pullback of etale
cocycles.

## Proof

Points have no higher etale cohomology, and finite disjoint unions commute
with every map under consideration. We may therefore take $C$ to be a
smooth connected curve. Let $\overline C$ be its smooth proper
compactification, of genus $g$, and let
$D=\overline C\setminus C$ consist of $r$ points.

Choose a primitive $\ell$th root in $k$, identifying
$\underline{\mathbf F_\ell}$ with $\mu_\ell$. The Kummer sequence

$$
1\longrightarrow\mu_\ell\longrightarrow\mathbf G_m
\xrightarrow{(\cdot)^\ell}\mathbf G_m\longrightarrow1
$$

gives

$$
H^1(\overline C,\mu_\ell)=\operatorname{Pic}(\overline C)[\ell],
\qquad
0\to\operatorname{Pic}(\overline C)/\ell
\to H^2(\overline C,\mu_\ell)\to
\operatorname{Br}(\overline C)[\ell]\to0.
$$

The degree sequence
$0\to\operatorname{Pic}^0(\overline C)(k)\to \operatorname{Pic}(\overline C)\to\mathbf Z\to0$
and the finite etale isogeny $[\ell]$ on the $g$-dimensional Jacobian give

$$
\operatorname{Pic}(\overline C)[\ell]\cong(\mathbf Z/\ell)^{2g},
\qquad
\operatorname{Pic}(\overline C)/\ell\cong\mathbf Z/\ell.
$$

The Brauer group ([def-br]) is zero. To expose the curve input, restriction injects it
into $\operatorname{Br}(k(\overline C))$ by the discrete-valuation residue
sequence. The latter group is zero because $k(\overline C)$ is $C_1$:
writing the unknowns as polynomials of degree at most $N$ turns a homogeneous
equation of degree $d$ in more than $d$ variables into fewer coefficient
equations than unknown coefficients for $N$ large; a nonzero solution over
the algebraically closed field gives a zero of the original form. Applied
to a reduced norm form, this splits every central simple algebra. The same
residue sequence and $\ell$-cohomological dimension one of this $C_1$ field
give $H^q(\overline C,\mu_\ell)=0$ for $q>2$. Consequently

$$
H^0(\overline C,\mathbf F_\ell)=\mathbf F_\ell,\quad
H^1(\overline C,\mathbf F_\ell)=(\mathbf F_\ell)^{2g},\quad
H^2(\overline C,\mathbf F_\ell)=\mathbf F_\ell.
$$

Purity for the finite set $D$ is the local DVR calculation: a parameter
$t$ identifies the boundary class with the valuation of an
$\ell$th-root Kummer torsor. It gives the exact localization segment

$$
\begin{aligned}
0&\longrightarrow H^1(\overline C,\mathbf F_\ell)
\longrightarrow H^1(C,\mathbf F_\ell)
\xrightarrow{\partial}H^0(D,\mathbf F_\ell(-1))\\
&\xrightarrow{\sum\operatorname{tr}_x}
H^2(\overline C,\mathbf F_\ell)
\longrightarrow H^2(C,\mathbf F_\ell)\longrightarrow0 .
\end{aligned}
$$

The trace sends the basis vector at each $x\in D$ to the fundamental class,
so when $r>0$ it is the summation map
$(\mathbf F_\ell)^r\to\mathbf F_\ell$ and is surjective. Thus a nonproper
smooth curve is affine,

$$
H^1(C,\mathbf F_\ell)\cong(\mathbf F_\ell)^{2g+r-1},
\qquad H^q(C,\mathbf F_\ell)=0\quad(q>1).
$$

Under an algebraically closed extension $k'/k$, the compactification, genus,
boundary points, Kummer sequence, valuation boundary $\partial$, trace, and
the displayed summation map all pull back to their primed counterparts.
Hence the vertical maps in the localization diagram are isomorphisms.
This proves assertions (1), (2), (4), (5), and (6), and assertion (7) in the
proper case. For assertion (8), an open in a proper connected curve is
either the whole curve or is affine with zero $H^2$; opens in an affine
curve are affine. The restriction $H^2(C)\to H^2(W)$ is therefore either
the identity or the unique map onto zero. All claimed maps are the maps in
the Kummer and localization sequences, so their naturality is fixed.
