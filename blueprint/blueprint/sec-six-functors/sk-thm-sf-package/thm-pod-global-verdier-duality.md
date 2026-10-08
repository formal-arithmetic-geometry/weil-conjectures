+++
id = "thm-pod-global-verdier-duality"
kind = "theorem"
title = "Global Verdier duality at the point"
order = 2248
uses = ["def-pod-conventions", "def-weil-finite-coefficient-point", "def-weil-ordinary-compact-cohomology", "def-weil-site-perfect-complex", "fix-cor-verdier-exchange", "lem-fix-operation-reduction", "lem-pod-point-dualizing-complex", "thm-pur-finite-reduction-of-purity", "thm-sf-global-duality"]
+++
Use the Poincare duality conventions of [def-pod-conventions] (so $X_0$
is smooth, separated of finite type and geometrically connected of pure
dimension $d$, not necessarily proper). The statement below also
holds verbatim for a smooth, proper, geometrically connected $k$-scheme
$X$ of pure dimension $d$ not assumed to descend to $k_0$ (see
[thm-sf-global-duality]). Let $K\in D^b_{ctf}(X,\Lambda)$. For the admissible structure
morphism $a_X:X\to s$ there is a canonical isomorphism

$$
R\Gamma_c(X,K)^\vee\xrightarrow{\sim}R\Gamma(X,\mathbb D_XK),
$$

with the cohomology functors
of the fixed coefficient stage. It is natural in $K$ and compatible
with shifts. For a site-perfect
$K$, it is also compatible with finite coefficient reduction and
scalar extension under the smooth orientation and its coefficient
comparisons. At $K=\Lambda_X$ it identifies
$R\Gamma_c(X,\Lambda_X)^\vee$ with $R\Gamma(X,\omega_{X,\Lambda})$.

## Proof

Apply the independently proved exchange [fix-cor-verdier-exchange]
to $f=a_X$ and the coefficient object at $s$:

$$
D_sRa_{X!}K\cong Ra_{X*}D_XK.
$$

By [lem-pod-point-dualizing-complex], $D_s$ is the derived
coefficient dual. Apply the point equivalence of
[def-weil-finite-coefficient-point]; the two resulting global
functors are those of [def-weil-ordinary-compact-cohomology].
This proves the asserted isomorphism and its naturality and shift
compatibility. Its construction uses only tensor–Hom adjunction,
the compact-support projection formula, and the adjunction for
$Ra_{X!}$; it does not use global Poincare duality.
For $K$ site-perfect in the sense of
[def-weil-site-perfect-complex], the tensor, internal-Hom,
evaluation, and cohomology comparisons are
[lem-fix-operation-reduction]. The smooth dualizing object and
its counit reduce compatibly by
[thm-pur-finite-reduction-of-purity]. Each constituent of the
adjunction comparison therefore commutes with coefficient change,
so their composite does too. Finally $D_X\Lambda_X=\omega_X$
by tensor–Hom evaluation of the unit object, giving the specialization.
Properness of $X_0$ is used nowhere above: the exchange
[fix-cor-verdier-exchange] needs only that $a_X$ is exceptionally
admissible, $Ra_{X!}$ and $Ra_{X*}$ enter as different functors with no
comparison between them, and the smooth dualizing object and its finite
reduction ([thm-pur-finite-reduction-of-purity]) are stated for smooth
separated morphisms. The same argument applies word for word to a smooth
proper $X$ over $k$ that is not defined over $k_0$, which is the proper
case of [thm-sf-global-duality].
