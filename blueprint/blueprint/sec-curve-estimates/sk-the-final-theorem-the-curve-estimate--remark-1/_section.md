+++
id = "sk-the-final-theorem-the-curve-estimate--remark-1"
kind = "section"
title = "Remark"
order = 1025
+++
*Remark (sketch).*

This is the final part of this section, used in [sk-thm-p1]

## Proof

$H^0(C,\Z/n)=H^0(C,\mu_n)=\mu_n(k)=\Z/n$ (algebraically closed,
primitive root). By [sk-prop-h1] ($C$ is proper), $H^1(C,\Z/n)=\Pic(C)[n]$; the
degree map splits $\Pic(C)=\Pic^0(C)\times\Z$ (a base point gives a
section) and $\Z$ is torsion-free, so
$\Pic(C)[n]=\Pic^0(C)[n]=J(C)[n]$, which is $(\Z/n)^{2g}$ by
[sk-prop-jacobian] and [sk-thm-av-final](c). By
[sk-prop-h2], $H^2(C,\Z/n)=\Pic(C)/n\Pic(C)=(\Z/n)\oplus J(C)/nJ(C) =\Z/n$ by [sk-thm-av-final](d) (the $\Z/n$ is the degree part).
The vanishing is [sk-prop-cd].

Uses: [sk-prop-cd], [sk-prop-h1], [sk-prop-h2], [sk-prop-jacobian], [sk-thm-av-final]
