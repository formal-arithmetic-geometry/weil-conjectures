+++
id = "sk-thm-curveestimate"
kind = "section"
title = "Curve estimate"
order = 1022
uses = ["sk-def-av-jacobian", "sk-def-av-pic", "sk-def-curve", "sk-def-kummer", "sk-def-pic", "sk-prop-cd", "sk-prop-h1", "sk-prop-h2", "sk-prop-jacobian", "sk-thm-av-final", "sk-thm-picard-duality", "sk-thm-picard-rr"]
+++
*Theorem (sketch).*

Let $C$ be smooth proper connected (hence of dimension $1$,
[sk-def-curve]; for $C=\Spec k$ one has $H^2(C,\Z/n)=0$ and the
statement is false) of genus $g$ over algebraically
closed $k$, and let $n$ be prime to $\operatorname{char}k$. After
choosing a primitive $n$-th root of unity (the identification
$\mu_n\cong\Z/n$ of étale sheaves), the constant-sheaf cohomology
of $C$ is

$$
H^0(C,\Z/n)=\Z/n,\qquad
H^1(C,\Z/n)=(\Z/n)^{2g},\qquad
H^2(C,\Z/n)=\Z/n,
$$

and $H^q(C,\Z/n)=0$ for $q\ge3$.

*Identifications used in the proof.* $H^1(C,\Z/n)=\Pic(C)[n]=\Pic^0(C)[n]=J(C)[n]$,
where $\Pic^0(C)$ is the kernel of the divisor degree of [sk-def-pic],
which is the $\Pic^0(C)$ of [sk-prop-jacobian], defined by the
$\chi$-degree, because the two degrees agree by [sk-thm-picard-rr](RR);
and the genus $g$ of [sk-def-curve], $\dim_kH^0(C,\Omega^1_{C/k})$, is
the dimension $\dim_kH^1(C,\cO_C)$ of $J(C)$ in [sk-prop-jacobian] by
[sk-thm-picard-duality].

Uses: [sk-def-curve], [sk-def-kummer], [sk-def-pic], [sk-prop-cd], [sk-prop-h1], [sk-prop-h2], [sk-prop-jacobian], [sk-thm-av-final], [sk-thm-picard-rr], [sk-thm-picard-duality]
