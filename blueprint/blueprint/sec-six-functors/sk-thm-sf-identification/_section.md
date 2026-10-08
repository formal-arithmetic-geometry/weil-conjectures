+++
id = "sk-thm-sf-identification"
kind = "section"
title = "The derived Poincaré pairing is the duality isomorphism"
order = 2182
uses = ["sk-lem-sf-twist-interchange", "sk-thm-sf-global-duality", "sk-thm-sf-tensor-hom"]
lean = ["AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_coefficientDual_of_orientation"]
+++
*Theorem (sketch).*

Let $X$ satisfy the hypotheses of [sk-thm-sf-global-duality],
with the orientation of [sk-def-sf-orientation] fixed, and let
$K\in\Dctf(X,\Lambda)$ be perfect over $\Lambda_X$. Then the tensor–internal-Hom
adjoint of the derived pairing

$$
\beta_K:\RG_c(X,K)\otimes^L_\Lambda\RG\bigl(X,K^\vee(d)\bigr)[2d]\to\Lambda
$$

is the canonical isomorphism
$\RG(X,K^\vee(d))[2d]\xrightarrow{\sim} R\mathrm{Hom}_\Lambda(\RG_c(X,K),\Lambda)$ *in the point category*
$\Dbc(s,\Lambda)$, and its inverse is the global
duality isomorphism of [sk-thm-sf-global-duality] followed by
$\mathbb D_XK\cong K^\vee(d)[2d]$. In particular $\beta_K$ is perfect.
If $X$ is proper and $\Lambda\in\{A_{E,n},E,\Qlb\}$, its degreewise form
gives perfect pairings
$\langle-,-\rangle_i:H^i_c(X,K)\times H^{2d-i}(X,K^\vee(d))\to\Lambda$
(over $A_{E,n}$ because this ring is self-injective, so
$\operatorname{Hom}(-,\Lambda)$ is exact). At the integral stage
$\Lambda=\mathcal O_E$ the degreewise form fails in general: a torsion
class in $H^i_c$ pairs to zero with everything, and
$H^{-i}(\RG_c^\vee)$ picks up an $\operatorname{Ext}^1$ term from the
torsion of $H^{i+1}_c$; only the derived statement holds there.
For nonproper $X$ the degreewise assertion over field coefficients is
recorded separately in [sk-thm-derived-duality].

## Proof

The pairing $\beta_K$ is the composite of the mixed-support cup product, the
evaluation $K\otimes^LK^\vee\to\Lambda_X$ (twisted), and the normalized trace,
i.e. the counit of $Ra_{X!}\dashv Ra_X^!$ read through the orientation. The
chain of [sk-thm-sf-tensor-hom] with $M=K$, $N=\Lambda$ and $f=a_X$ is, by
[sk-lem-sf-mate], the transpose of exactly that composite; hence the adjoint
of $\beta_K$ is the composite of the duality isomorphism with the orientation
identification, which is an isomorphism. Degreewise this is the shift
convention together with $H^{-i}(C^\vee)\cong H^i(C)^\vee$ for a perfect point
complex, which holds when $\operatorname{Hom}(-,\Lambda)$ is exact, i.e. for
$\Lambda\in\{A_{E,n},E,\Qlb\}$.

Uses: `\Cref{lem-sf-twist-interchange}`, `\Cref{thm-sf-global-duality}`, `\Cref{sk-thm-sf-tensor-hom}`, `def-coefficient-twists-detailed`, `def-weil-poincare-trace-cup`
