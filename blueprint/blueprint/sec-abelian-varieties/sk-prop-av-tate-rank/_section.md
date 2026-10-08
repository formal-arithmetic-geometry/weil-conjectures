+++
id = "sk-prop-av-tate-rank"
kind = "section"
title = "The $\\ell$-adic Tate module is free of rank $2g$"
lean = ["AlgebraicGeometry.IsAbelianScheme.nonempty_linearEquiv_tateModule"]
order = 590
uses = ["sk-def-av", "sk-def-av-tate", "sk-prop-av-divisible", "sk-prop-av-ntorsion-etale"]
+++
*Proposition (sketch).*

Let $A$ be an abelian variety of dimension $g$ over an algebraically
closed field $k$ and let $\ell\ne\operatorname{char}k$. Then

$$
T_\ell A\cong\Z_\ell^{2g},\qquad V_\ell A\cong\Q_\ell^{2g}.
$$

## Proof

By [sk-prop-av-ntorsion-etale] each level is
$A[\ell^n](k)\cong(\Z/\ell^n\Z)^{2g}$, and by [sk-prop-av-divisible]
the transition map $[\ell]:A[\ell^{n+1}](k)\to A[\ell^n](k)$ is
surjective. Choosing compatible bases through these surjections
identifies the inverse system defining $T_\ell A$
([sk-def-av-tate]) with the system
$(\Z/\ell^n\Z)^{2g}$ under reduction, whose limit is $\Z_\ell^{2g}$;
tensoring with $\Q_\ell$ gives $V_\ell A\cong\Q_\ell^{2g}$.

Uses: [sk-def-av-tate], [sk-def-av], [sk-prop-av-divisible], [sk-prop-av-ntorsion-etale]
