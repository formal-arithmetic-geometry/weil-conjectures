+++
id = "sk-prop-h2"
kind = "section"
title = "$H^2$ via Kummer"
order = 930
uses = ["sk-def-av-pic", "sk-def-br", "sk-def-kummer", "sk-def-pic", "sk-prop-kummer-exact", "sk-thm-br"]
+++
*Proposition (sketch).*

For $C$ a *smooth proper* curve as in [sk-def-curve] and every
$n\ge1$ prime to $\operatorname{char}k$:

$$
H^2(C,\mu_n)\cong\Pic(C)/n\cdot\Pic(C).
$$

(The identity in fact holds for every curve of [sk-def-curve],
because $\Br(C)=0$ for all of them; but the proof below uses
[sk-thm-br], which is stated for smooth proper curves, and the
smooth proper case is all that is used. The smooth affine case is
rederived where it is needed, from [sk-prop-br-inj] and
[sk-prop-tsen].)

## Proof

In the same long exact sequence of [sk-def-kummer], exact by
[sk-prop-kummer-exact] (with
$H^1(C,\mathbb G_m)=\Pic(C)$ by [sk-def-pic] and the last term
$H^2(C,\mathbb G_m)=\Br(C)=0$ by [sk-thm-br], $C$ being smooth
proper) the displayed quotient is the cokernel of
$n:\Pic(C)\to\Pic(C)$.

Uses: [sk-def-br], [sk-def-kummer], [sk-def-pic], [sk-prop-kummer-exact], [sk-thm-br]
