+++
id = "sk-d-pairing"
kind = "section"
title = "The supported pairing recipe"
order = 2308
uses = ["sk-d-corr", "sk-d-integral", "sk-d-six", "sk-thm-sf-kunneth-verdier"]
lean = ["AlgebraicGeometry.ProEtale.GeometricOperations.supportedPairing"]
+++
*Definition (sketch).*

For an opposite pair, use the inverse
Künneth–Verdier maps to obtain

$$
\widetilde u:Rc_!A_C\to P=L\boxt D_XK,
\qquad \widetilde v:R\bar d_!A_D\to Q=D_YL\boxt K.
$$

If $e:E(C,D)\to Z$, the projection formula and $!$-base change
give $Re_!A_E\simeq Rc_!A_C\otimes R\bar d_!A_D$.
Compose with $\widetilde u\otimes\widetilde v$, then the two Verdier
evaluations and $\omega_Y\boxt\omega_X\simeq\omega_Z$.
Its exceptional adjoint is the Borel–Moore section
$\langle u,v\rangle_{\mathrm{LV}}:A_E\to\omega_E$.

Uses: [sk-d-corr], [sk-d-integral], [sk-d-six], [sk-thm-sf-kunneth-verdier]
