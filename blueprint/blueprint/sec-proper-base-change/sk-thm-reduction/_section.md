+++
id = "sk-thm-reduction"
kind = "section"
title = "Reduction to $\\Pone$"
order = 1184
lean = ["AlgebraicGeometry.Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper"]
uses = ["sk-def-conv", "sk-def-pbc", "sk-thm-chow", "sk-thm-groth-ss", "sk-thm-iff", "sk-thm-p1"]
+++
*Theorem (sketch).*

Assume that $\Pone_S\to S$ satisfies $\mathrm{PBC}$ for every scheme
$S$ (in the sense of [sk-def-pbc]). Then every
proper morphism of schemes satisfies
$\mathrm{PBC}$.

## Proof

We use the following elementary manipulations, each argued where it
occurs: finite morphisms satisfy PBC; PBC composes; PBC cancels
along a proper surjection; $\Pone$ gives $\Pqn$; PBC is étale
local on the target.

*Reduction to an affine base.* For quasi-compact
quasi-separated $f$, the restriction of $R^qf_*F$ to an étale
$V\to Y$ is the sheafification of
$U\mapsto H^q(X\times_YU,F|)$, compatible with exchange; exchange is
therefore an isomorphism iff it is one over the geometric points of
an étale cover of $Y$, and geometric stalks are conservative: PBC
is étale local on the target, so we may assume $Y$ affine.

*Chow's factorization.* By [sk-thm-chow] there are
$\pi:\widetilde X\to X$ proper surjective and a closed immersion
$i_Y:\widetilde X\hookrightarrow\Pqn_Y$ with $f\pi=q_Yi_Y$; the
graph map $i_X=(\pi,i_Y):\widetilde X\hookrightarrow\Pqn_X$ is a
closed immersion over $X$, so $\pi=q_Xi_X$.

*Closed immersions are finite, and finite morphisms satisfy
PBC.* After base change to the strict henselization at a geometric
point $\bar y$ the finite fibre is a finite disjoint union of
strictly henselian local schemes, whence
$(f_*F)_{\bar y}=\prod_{\bar x\to\bar y}F_{\bar x}$ as a finite
product; $f_*$ is exact, $R^qf_*=0$ for $q>0$, exchange is the
identity summand-wise, and the same holds after every base change.
Thus $\mathrm{PBC}(i_X)=\mathrm{PBC}(i_Y)$.

*From $\Pone$ to $\Pqn$.* The symmetric-product morphism

$$
\sigma_n:(\Pone_S)^n\to\Pqn_S,\quad
([x_i:y_i])_i\mapsto[F_0:\dots:F_n],\ \
\textstyle\prod_{i=1}^n(x_it+y_i)=\sum_jF_jt^j,
$$

is finite (each $z_i=x_i/y_i$ is integral over the elementary
symmetric subring) and surjective (over an algebraically closed
field every binary form of degree $n$ factors into linear forms).
The projection $(\Pone_T)^n\to T$ is a composite of $n$
projective-line projections over successive bases: by
[sk-thm-p1] and the composition step below it satisfies PBC;
$\sigma_n$ being finite satisfies PBC; and since the composite
$(\Pone_T)^n\to\Pqn_T\to T$ is the product projection, cancellation
along the surjective $\sigma_n$ (below) gives PBC for
$\Pqn_T\to T$.

*Composition.* If $f,h$ are proper with $\mathrm{PBC}(f)$,
$\mathrm{PBC}(h)$, then $\mathrm{PBC}(hf)$: convert both to
$\mathrm{IA}$ via [sk-thm-iff]; $f_*I$ is injective for $I$
injective ($f_*$ is right adjoint to the exact $f^{-1}$), the
$q>0$ higher direct images of $a^{-1}I$ along $f'$ vanish, and the
conjugates are identified by the degree-zero exchange used in
[sk-thm-iff]; in the spectral sequence [sk-thm-groth-ss] for
the composite only the $q=0$ row survives, killed in positive
degrees by $\mathrm{IA}(h)$; convert back. Hence
$\mathrm{PBC}(\pi)$ ($\pi=q_Xi_X$) and $\mathrm{PBC}(f\pi)$
($f\pi=q_Yi_Y$).

*Cancellation.* If $f$ is proper surjective with
$\mathrm{PBC}(f)$, $\mathrm{PBC}(hf)$, then $\mathrm{PBC}(h)$:
convert to $\mathrm{IA}$; an injective $I$ on $Y$ embeds
$I_{\bar y}\hookrightarrow J_{\bar x}$ into an injective $J$ on $X$
over the fibre, so $I\to f_*J$ splits and $I$ is a direct summand
of $f_*J$; by the spectral sequence [sk-thm-groth-ss] together
with $\mathrm{IA}(f)$ and $\mathrm{IA}(hf)$ the higher direct
images of $b^{-1}f_*J\cong f'_*a^{-1}J$ vanish, and vanishing passes
to direct summands; convert back. [sk-thm-p1] supplies the
hypothesis, so cancel $\pi$: $\mathrm{PBC}(f)$.

Uses: [sk-def-conv], [sk-def-pbc], [sk-thm-chow], [sk-thm-groth-ss], [sk-thm-iff], [sk-thm-p1]
