+++
id = "sk-prop-normal-form"
kind = "section"
title = "Étale-local normal form and slicing"
order = 1397
uses = ["sk-def-smooth"]
lean = ["AlgebraicGeometry.Smooth.exists_etale_to_affineSpace", "AlgebraicGeometry.exists_etaleCover_factorization"]
+++
*Proposition (sketch).*

Let $g:X\to Y$ be smooth at $x\in X$, of relative dimension $d$
there. Then, after replacing $X$ and $Y$ by affine neighbourhoods,
$g$ factors as

$$
X\ \xrightarrow{\ e\ }\ \Aaf^d_Y\ \xrightarrow{\ p_d\ }\ Y
$$

with $e$ étale and $p_d$ the projection. Moreover, for any smooth
$f:X\to S$ there is an étale covering $\{U_i\to X\}_{i\in I}$ such
that each $U_i\to S$ factors as

$$
U_i\longrightarrow V_i\longrightarrow S
$$

with $V_i\to S$ étale and $U_i\to V_i$ smooth affine with
geometrically connected fibres and a section.
(Stacks Project, Tags `054L` and `0EY4`.)

## Proof

*Normal form.* Shrinking to affines, write $X=\Spec B$,
$Y=\Spec A$ with $B=A[t_1,\dots,t_n]/(g_1,\dots,g_c)$ and the
Jacobian $(\partial g_i/\partial t_j)$ of rank $c=n-d$ at $x$. Pick
$d$ of the coordinates whose differentials complete the $c$ rows of
the Jacobian to a basis of
$\Omega_{A[t]/A}\otimes\kappa(x)$; they define a $Y$-morphism
$e:X\to\Aaf^d_Y$ with $\Omega_{X/\Aaf^d_Y}=0$ near $x$, i.e. $e$
unramified. Source and target are smooth over $Y$ of the same
relative dimension $d$, but $Y$ is arbitrary, so miracle flatness
cannot be applied to $e$ itself; apply it fibrewise. For $y\in Y$
the fibre $e_y:X_y\to\Aaf^d_{\kappa(y)}$ is an unramified morphism of
smooth $\kappa(y)$-schemes of dimension $d$; its fibres are
$0$-dimensional, and the local rings at $x$ and $e(x)$ are regular of
the same dimension (unramified morphisms have finite residue
extensions, so $x$ and $e(x)$ have the same transcendence degree over
$\kappa(y)$), so miracle flatness (regular target, Cohen–Macaulay
source, $\dim$ source $=\dim$ target $+$ fibre dimension) makes $e_y$
flat at $x$. Since $X$ and $\Aaf^d_Y$ are flat and locally of finite
presentation over $Y$, the fibrewise flatness criterion makes $e$
flat at $x$, and flat $+$ unramified $=$ étale. (Equivalently: a
$Y$-morphism of $Y$-smooth schemes is étale at $x$ as soon as it
induces an isomorphism on $\Omega_{-/Y}\otimes\kappa(x)$, which the
choice of coordinates guarantees.) Composing with $p_d$ returns $g$
by construction.

*Slicing and relative connectedness.* Let $x\in X$ be a point
*closed in its own fibre* $X_s$, $s=f(x)$, *with
$\kappa(x)/\kappa(s)$ separable*. Then
$\mathfrak m_x/\mathfrak m_x^2$ computed in the smooth
$\kappa(s)$-scheme $X_s$ has dimension $d=\dim_xX_s$ and maps
isomorphically onto
$\Omega_{X_s/\kappa(s)}\otimes\kappa(x)=\Omega_{X/S}\otimes\kappa(x)$
(the cokernel of this map is $\Omega_{\kappa(x)/\kappa(s)}$, which
vanishes exactly because the finite extension is separable; without
separability no such sections exist, e.g. $S=\Spec\mathbf F_p(t)$,
$X=\Aaf^1_S$, $x$ given by $u^p=t$), so one may cut
$X$ near $x$ by $d$ sections of $\mathcal O_X$ vanishing at $x$ whose
differentials are a basis of $\Omega_{X/S}\otimes\kappa(x)$; the
resulting closed subscheme
$V\subseteq X$ is smooth of relative dimension $0$ over $S$ at $x$ by
the Jacobian
criterion, i.e. étale there, so after shrinking $V\to S$ is
étale and $(\iota,\mathrm{id}):V\to X\times_SV$ is a section of the
smooth $X\times_SV\to V$. Let $U\subseteq X\times_SV$ be the
relative connected component of that section, i.e. the set of points
lying in the same connected component of their own fibre as the
section; it is open by the open representability of the relative
connected-component functor for a flat, finitely presented morphism
with geometrically unibranch (here: smooth) fibres. Then $U\to V$
is smooth with geometrically connected fibres and a section, $V\to S$
is étale, and $U\to X\times_SV\to X$ is étale. These $U$ cover
$X$: the image $W_x$ of $U\to X$ is open and contains the whole
connected component of $x$ in $X_s$, because the fibre of $U$ over
the point $x\in V$ is the connected component of
$X_s\otimes_{\kappa(s)}\kappa(x)$ through the section point, and the
finite étale surjection $X_s\otimes_{\kappa(s)}\kappa(x)\to X_s$
($\kappa(x)/\kappa(s)$ finite separable) maps connected components
onto connected components. Connected components of the locally
noetherian $X_s$ are open, and every nonempty open of the smooth
$\kappa(s)$-scheme $X_s$ contains a point closed in $X_s$ with
separable residue field (by the normal form it contains an open
étale over $\Aaf^d_{\kappa(s)}$, whose points with coordinates in a
separable closure are dense, and étale maps have separable residue
extensions). Hence every connected component of every fibre lies in
some $W_x$, and $\bigcup_xW_x=X$.

Uses: [sk-def-smooth]
