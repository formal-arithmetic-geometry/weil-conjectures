+++
id = "sk-p-dl-a1-some-weight"
kind = "section"
title = "The generic Fourier sheaf is pure of some weight"
order = 2770
uses = ["sk-p-dl-a1-correction", "sk-p-real-purity", "sk-p-real-semi", "sk-prop-kernel-lisse", "sk-thm-fourier-trace-formula"]
lean = ["AlgebraicGeometry.exists_isPunctuallyPureOfWeight_of_isFourierPartner"]
+++
*Proposition (sketch).*

For nonexceptional $M$ pure of weight $w$, the irreducible sheaf $M'$
in [sk-p-dl-a1-middle] is pure of some real weight $v$.

## Proof

Set $M^c=M^\vee\otimes T_w$, where the Frobenius scalar of $T_w$ maps
to $q^w$ under $\iota$. On a common dense lisse open the paired complex

$$
\DLAFT_\psi(j_!M[1])\oplus
\DLAFT_{\psi^{-1}}(j_!M^c[1])
$$

is $H[1]$ for a lisse sheaf $H$. Zero extension preserves conjugacy
of all point traces, including at the missing points where both
stalks are zero. The Fourier trace identity yields

$$
\iota t_{H,n}(y)=-\sum_{x\in U_0(\mathbf F_{q^n})}
\left(a_x\psi_n(xy)+\overline{a_x}\psi_n(xy)^{-1}\right),
\qquad a_x=\iota t_{M,n}(x).
$$

This is real for every finite extension. At a fixed closed point, all
Frobenius power traces are therefore real; Newton identities imply
that its characteristic polynomial is real. Hence $H$ is $\iota$-real.
The correction sequence makes $M'$ on this open an irreducible
constituent of $H$, so real-sheaf purity gives a weight $v$.
Semicontinuity applied to $M'$ and its lisse dual extends purity to
its full lisse domain. Forming the envelope after zero extension is
what avoids assuming reality of $j_*M$.

Uses: [sk-p-dl-a1-correction], [sk-p-real-purity], [sk-p-real-semi], [sk-thm-fourier-trace-formula]
