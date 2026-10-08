+++
id = "prop-av-tate-rank"
kind = "theorem"
title = "The $\\ell$-adic Tate module is free of rank $2g$"
lean = ["AlgebraicGeometry.IsAbelianScheme.nonempty_linearEquiv_tateModule"]
order = 591
uses = ["def-sc-abelian-variety", "def-wf-abelian-tate-module", "lem-sc-isogeny-surjective", "lem-sc-ntorsion-etale"]
tags = ["latex:proposition"]
+++
Let $A$ be an abelian variety ([def-sc-abelian-variety]) of dimension $g$ over an algebraically
closed field $k$ and let $\ell\ne\operatorname{char}k$. Then

$$
T_\ell A\cong\Z_\ell^{2g},\qquad V_\ell A\cong\Q_\ell^{2g}.
$$

## Proof

By [lem-sc-ntorsion-etale] each level is
$A[\ell^n](k)\cong(\Z/\ell^n\Z)^{2g}$, and the transition map $[\ell]:A[\ell^{n+1}](k)\to A[\ell^n](k)$ is
surjective, since $A(k)$ is divisible by [lem-sc-isogeny-surjective]
(an $\ell$-th root of a point of $A[\ell^n](k)$ lies in $A[\ell^{n+1}](k)$). Choosing compatible bases through these surjections
identifies the inverse system defining $T_\ell A$
([def-wf-abelian-tate-module]) with the system
$(\Z/\ell^n\Z)^{2g}$ under reduction, whose limit is $\Z_\ell^{2g}$;
tensoring with $\Q_\ell$ gives $V_\ell A\cong\Q_\ell^{2g}$.

Uses: [def-sc-abelian-variety], [def-wf-abelian-tate-module], [lem-sc-isogeny-surjective], [lem-sc-ntorsion-etale]
