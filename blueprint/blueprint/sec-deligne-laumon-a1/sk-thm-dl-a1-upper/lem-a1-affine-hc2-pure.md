+++
id = "lem-a1-affine-hc2-pure"
kind = "lemma"
title = "Purity of $H_c^2$ on an affine curve"
order = 2786
uses = ["def-weil-frobenius-module-weights", "def-weil-ordinary-compact-cohomology", "def-weil-punctual-weights", "lem-a1-affine-hc2", "lem-a1-geometric-coinvariants-pure", "lem-wf-tate-twist-frobenius"]
+++
Let $U_0$ be a smooth geometrically connected affine curve and let
$\mathcal F$ be a lisse Weil sheaf on $U_0$ which is punctually
$\iota$-pure of weight $w$. Then $H_c^2(U,\mathcal F)$, with its
Frobenius, is $\iota$-pure of weight $w+2$ in the sense of
[def-weil-frobenius-module-weights] (the zero module being pure of
every weight).

## Proof

By [lem-a1-affine-hc2] there is a canonical Frobenius-equivariant
isomorphism $H_c^2(U,\mathcal F)\simeq W(-1)$, where
$W=V_{\pi_1(U)}$ is the coinvariant quotient of the geometric generic
stalk $V=\mathcal F_{\bar\eta}$ under the geometric fundamental group.

*The coinvariants are pure of weight $w$.* The curve $U_0$ is smooth
and geometrically connected, in particular nonempty, so
[lem-a1-geometric-coinvariants-pure] shows that $W$ with its induced
Frobenius $F_W$, the Frobenius of the coinvariants in
[lem-a1-affine-hc2], is $\iota$-pure of weight $w$.

*The twist.* By [lem-wf-tate-twist-frobenius] the geometric Frobenius
acts on the twist $\Qlb(-1)$ by multiplication by $q$, so the Frobenius
of $W(-1)$ is $qF_W$, whose eigenvalues $q\lambda$ have
$\iota$-modulus $q\cdot q^{w/2}=q^{(w+2)/2}$. Hence
$H_c^2(U,\mathcal F)\simeq W(-1)$ is $\iota$-pure of weight $w+2$.
