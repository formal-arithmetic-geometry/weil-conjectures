+++
id = "thm-pur-general-admissibility"
kind = "theorem"
title = "Preservation for an affine base, modulo the open-complement condition"
order = 2078
uses = ["cor-exc-base-change-open-immersion-general", "cor-pur-smooth-admissibility", "cor-sf-ambient-adjoint-discharge", "def-exc-open-complement-bound", "def-pur-conventions", "def-sbc-affine-space", "def-weil-ambient-exceptional-adjoint", "def-weil-constructible-intervals", "def-weil-exceptional-adjoint-admissibility", "def-weil-finite-tor-amplitude", "def-weil-scheme-morphism-properties", "lem-exc-closed-ambient", "lem-exc-closed-amplitude", "prop-exc-closed-tor", "prop-exc-open-adjoint", "thm-exc-explicit-preservation"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $f:X\to Y$ be a
separated finite-type
morphism. The
ambient exceptional right
adjoint datum of [def-weil-ambient-exceptional-adjoint] was the
hypothesis under which this theorem was formerly stated; it is not assumed
here, the right adjoints $Rf^{\times}$, $R(\pi_U)^{\times}$,
$R(i_U)^{\times}$ that the proof forms being available on the bounded
constructible and finite-Tor coefficients of the two clauses below by
[cor-sf-ambient-adjoint-discharge]. Cover $Y$ by finitely
many affine opens $V\subseteq Y$; for each $V$, $f^{-1}(V)$ is
covered by finitely many affine opens $U\subseteq f^{-1}(V)$, and each
$U\to V$ is affine of finite type, hence a closed subscheme of
$\mathbf A^{d_U}_V$ for some $d_U\in\mathbf Z_{\geq0}$, with open
complement $W_U=\mathbf A^{d_U}_V\setminus U$ in the
[def-sbc-affine-space] affine space. Assume the open-complement
condition of [def-exc-open-complement-bound] for every pair
$(W_U,\mathbf A^{d_U}_V)$ over the finitely many charts, with constants
$c_U$, and put $D=\max_U d_U$ and
$c=\max_U\bigl(c_U+1+2(D-d_U)\bigr)$. Then $f$
satisfies the two preservation clauses of
[def-weil-exceptional-adjoint-admissibility]:

1. for all integers $a\leq b$,
$$
L\in D_c^{[a,b]}(Y,A)\quad\Longrightarrow\quad
Rf^!L\in D_c^{[a-2D,b-2D+c]}(X,A);
$$
1. if $K\in D^b_{ctf}(Y,A)$ has
finite Tor amplitude in
$[a,b]$, then $Rf^!K$ has finite Tor amplitude in
$[a-2D,b-2D+c]$; in particular $Rf^!$ carries
$D^b_{ctf}(Y,A)$ into $D^b_{ctf}(X,A)$.

## Proof

On a chart $U\subseteq f^{-1}(V)$ with $V$ affine the morphism
$U\to V$ is affine of finite type, so the presentation of its
coordinate ring as a quotient of a polynomial algebra over
$\mathcal O_V(V)$ exhibits it as a closed subscheme
$i_U:U\hookrightarrow\mathbf A^{d_U}_V$ ([def-sbc-affine-space]);
write $\pi_U:\mathbf A^{d_U}_V\to V$ for the projection and
$u_U:U\hookrightarrow X$ for the open immersion (an open immersion, since
$U\subseteq f^{-1}(V)\subseteq X$), so that $fu_U=\pi_Ui_U$.
Step 1: the right adjoint of the chart. The compact-support direct image
of a composite is the composite of the compact-support direct images, and
the right adjoint of a composite of functors is the composite of their
right adjoints, so

$$
R(fu_U)^{\times}\;\cong\;R(i_U)^{\times}\circ R(\pi_U)^{\times},
\qquad
Lu_U^*\circ Rf^{\times}\;\cong\;R(fu_U)^{\times},
$$

the second because $R(u_U)_!=u_{U!}$ has right adjoint $Lu_U^*$ by
[prop-exc-open-adjoint]. Hence it suffices to bound
$R(i_U)^{\times}R(\pi_U)^{\times}$.
Step 2: the chartwise bounds. Fix $V$ and a chart $U\subseteq f^{-1}(V)$, and write $d=d_U$, $c'=c_U$. The projection $\pi_U$ is
smooth of pure relative dimension $d$, so
[cor-pur-smooth-admissibility] gives, for
$L\in D_c^{[a,b]}(V,A)$,

$$
R(\pi_U)^{\times}L\in D_c^{[a-2d,b-2d]}(\mathbf A^{d}_V,A),
$$

and for $K$ with finite Tor amplitude in $[a,b]$, finite Tor amplitude
in $[a-2d,b-2d]$; the closed immersion $i_U$ has ambient right
adjoint $R(i_U)^{\times}$ by [lem-exc-closed-ambient], and the
closed-support computations [lem-exc-closed-amplitude] and
[prop-exc-closed-tor], applied to the pair $(i_U,W_U)$ under the
assumed open-complement condition, move the interval to
$[a-2d,b-2d+c'+1]$. The exact restriction $Lu_U^*$ preserves both
kinds of bound ([thm-exc-explicit-preservation] for the open immersion $u_U$), so each chart carries the interval
$[a-2d_U,b-2d_U+c_U+1]$, which is contained in
$[a-2D,b-2D+c]$ by the choice of $D$ and $c$.
Step 3: passage from the affine opens of the base to the base. For an
affine open $V\subseteq Y$ with open immersion $g_V:V\hookrightarrow Y$
and $f_V:f^{-1}(V)\to V$, the base-change comparison for the open
immersion $g_V$ is an isomorphism by
[cor-exc-base-change-open-immersion-general], i.e.
$Rf_V^{\times}\cong Lg_V^*\circ Rf^{\times}$; that statement is read on the
coefficients of the present theorem, where the ambient datum it displays as a
hypothesis is the theorem [cor-sf-ambient-adjoint-discharge], so that
the comparison used here is unconditional, and both sides are applied only to
the bounded constructible complexes $Lg_V^*K$ with
$K\in D_c^{[a,b]}(Y,A)$. Applying Step 2 to the
separated finite-type morphism $f_V$ over the affine scheme $V$
therefore bounds $Lg_V^*(Rf^{\times}K)\cong Rf_V^{\times}(Lg_V^*K)$ on
$f^{-1}(V)$, hence on each chart $U\subseteq f^{-1}(V)$.
Step 4: conclusion. Vanishing of a cohomology sheaf, and vanishing of the
cohomology of a complex tensored with a coefficient sheaf, are local on the
site, and the charts $U$ cover $X$; hence the chartwise bounds of
Steps 2–3 give the two displayed assertions for the global object
$Rf^{\times}K$.
