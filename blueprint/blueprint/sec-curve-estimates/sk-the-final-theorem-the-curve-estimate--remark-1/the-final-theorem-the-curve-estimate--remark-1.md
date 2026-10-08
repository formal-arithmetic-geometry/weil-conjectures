+++
id = "the-final-theorem-the-curve-estimate--remark-1"
kind = "remark"
order = 1026
+++
This is the final part of this section, used in [prop-weil-pbc-projective-line]

## Proof

$H^0(C,\Z/n)=H^0(C,\mu_n)=\mu_n(k)=\Z/n$ (algebraically closed,
primitive root). By [lem-sc-kummer-les] ($C$ is proper), $H^1(C,\Z/n)=\Pic(C)[n]$; the
degree map splits $\Pic(C)=\Pic^0(C)\times\Z$ (a base point gives a
section) and $\Z$ is torsion-free, so
$\Pic(C)[n]=\Pic^0(C)[n]=J(C)[n]$, which is $(\Z/n)^{2g}$ by
[thm-sc-jacobian-representability] and [thm-av-final](c). By
[lem-sc-second-kummer-divisors], $H^2(C,\Z/n)=\Pic(C)/n\Pic(C)=(\Z/n)\oplus J(C)/nJ(C) =\Z/n$ by [thm-av-final](d) (the $\Z/n$ is the degree part).
The vanishing is [lem-sc-arbitrary-curve-cd].

Uses: [thm-av-final], [lem-sc-arbitrary-curve-cd], [lem-sc-kummer-les], [lem-sc-second-kummer-divisors], [thm-sc-jacobian-representability]
