+++
id = "sk-def-set"
kind = "section"
title = "The fixed setting"
order = 2404
uses = ["sk-def-sf-operations", "sk-def-sf-setting", "sk-prop-sf-existence", "sk-prop-sf-rf-shriek-preservation", "sk-thm-sf-ctf-stability"]
lean = ["AlgebraicGeometry.PoincareDualitySetting"]
+++
*Remark (sketch).*

Work with the finite-field datum $(p,a,q,k_0,k)$, $\ell$, $E$, $\Oe$,
$\varpi_E$, $\AEn=\Oe/\varpi_E^n$ and the coefficient stages
$\Lambda\in\{\AEn,\Oe,E,\Qlb\}$ fixed in [sk-def-sf-setting]. Let $X_0/k_0$ be smooth, separated of
finite type and geometrically connected of pure dimension $d$, put
$X=X_0\times_{k_0}k$ and $s=\Spec k$, and let $a_X:X\to s$ be the
structure morphism. No admissibility hypothesis is imposed on $a_X$: its
exceptional inverse image $Ra_X^!$ is the constructible exceptional adjoint
of [sk-def-sf-operations](vi), which exists and preserves
$\Dctf$ at every stage for every separated finite-type morphism
([sk-prop-sf-existence](c), [sk-prop-sf-rf-shriek-preservation],
[sk-thm-sf-ctf-stability](v)), so that what earlier versions assumed as
"exceptional-adjoint admissible at every stage" is a theorem here; the
ambient datum of [sk-def-sf-admissible], which fails for smooth proper
curves ([sk-rem-sf-fullcd-scope]), is not used. Properness of $X_0$ is *not* part of this setting: the
duality results [sk-thm-sf-global-duality], [sk-thm-sf-identification]
and [sk-thm-derived-duality]
are formulated with compact supports and never use it. It is imposed
explicitly, and only, in [sk-def-trace-cup], [sk-cor-trace],
[sk-thm-poincare-duality] and the final clause of
[sk-thm-derived-duality], each of which needs
$Ra_{X!}\cong Ra_{X*}$. (Blueprint 15, def:pod-conventions; the axioms are those of
13, def:sf-datum.)
