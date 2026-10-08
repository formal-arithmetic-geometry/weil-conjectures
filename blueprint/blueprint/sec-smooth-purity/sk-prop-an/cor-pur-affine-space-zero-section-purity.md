+++
id = "cor-pur-affine-space-zero-section-purity"
kind = "theorem"
title = "Zero-section purity in affine space"
order = 1981
tags = ["latex:corollary"]
uses = ["cor-amb-affine-space-adjunction", "cor-pur-affine-space-purity", "def-amb-p1-trace", "def-coefficient-twists-detailed", "def-pur-affine-space-comparison", "def-pur-conventions", "def-sbc-affine-space", "def-weil-exceptional-inverse-image", "def-weil-scheme-morphism-properties", "lem-amb-cartier-kummer-map", "lem-pur-kunneth-supported", "lem-pur-support-localization-triangle", "prop-asd-smooth-base-change", "prop-pur-affine-line-orientation-base-change", "thm-pur-affine-line-orientation", "thm-pur-affine-line-purity", "thm-sf-ambient-adjoint-class"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
$A=A_{E,n}$, let $B$ be a
separated finite-type
$k$-scheme and let $z:B\hookrightarrow\mathbf A^c_B$ be the zero
section of the affine space of [def-sbc-affine-space]. The
$c$-fold exterior product of the normalized affine-line orientation of
[thm-pur-affine-line-orientation] is a canonical, base-change
compatible isomorphism

$$
\Lambda_B\xrightarrow{\ \sim\ }Rz^!\Lambda_{\mathbf A^c_B}(c)[2c],
$$

i.e. $Rz^!\Lambda\cong\Lambda_B(-c)[-2c]$; the product of the Kummer
boundaries of the coordinates $t_1,\dots,t_c$ corresponds to $1$.
Moreover this isomorphism is the inverse of the composite
$Rz^!\Lambda_{\mathbf A^c_B}(c)[2c]\xrightarrow{Rz^!(\gamma_{p_c,\Lambda_B})}
Rz^!Rp_c^!\Lambda_B\cong\Lambda_B$, where $\gamma_{p_c,\Lambda_B}$ is the
affine-space purity comparison of [def-pur-affine-space-comparison]
(an isomorphism by [cor-pur-affine-space-purity]) and the last
identification is the composition law for $p_cz=\operatorname{id}_B$:
the affine-space purity comparison, restricted along the zero section,
is normalized by the product of the Kummer boundaries of the
coordinates. Equivalently, the integration map transposed from
$\gamma_{p_c,\Lambda_B}$ sends the class of the zero section,
$\partial\kappa(t_1)\cup\cdots\cup\partial\kappa(t_c)$, to $1$.

## Proof

First work on the ordinary etale site. The explicit adjunction of
[cor-amb-affine-space-adjunction] gives
$p_c^\times\Lambda_B=\Lambda_{\mathbf A^c_B}(c)[2c]$.
Composition of adjunctions, as in
[def-weil-exceptional-inverse-image], and
$p_cz=\operatorname{id}_B$ therefore identify
$Rz^!\Lambda_{\mathbf A^c_B}(c)[2c]$ with $\Lambda_B$.
In rank one this is the supported coordinate orientation: the
Cartier map of [lem-amb-cartier-kummer-map] integrates to $1$
under [def-amb-p1-trace], which is the normalization of
[thm-pur-affine-line-orientation]. Iterating the affine-line
adjunctions, the corresponding section classes are the ordered
product of these Cartier maps; their residues multiply to $1$.
The even shifts and twists add by [def-coefficient-twists-detailed].
The comparison [thm-sf-ambient-adjoint-class] transports the
composition and counits to the stated finite etale-origin objects.
Finally the rank-one orientations commute with base change by
[prop-pur-affine-line-orientation-base-change], and all the Cartier maps
and the explicit affine-space counits commute with base change, by
[lem-amb-cartier-kummer-map], [prop-asd-smooth-base-change].
Hence the resulting zero-section isomorphism has the claimed
normalization and base-change compatibility. No general relative
Kunneth assertion with closed support is needed for this calculation.
Finally, $\gamma_{p_c,\Lambda_B}$ is the transpose of the composite
affine-line adjunction ([thm-pur-affine-line-purity] identifies each
affine-line comparison with the adjoint of the normalized trace, and
[def-pur-affine-space-comparison] composes them along the tower), so
the identification $Rz^!\Lambda_{\mathbf A^c_B}(c)[2c]\cong\Lambda_B$
obtained above from $p_c^\times\Lambda_B=\Lambda_{\mathbf A^c_B}(c)[2c]$
and $p_cz=\operatorname{id}_B$ is exactly $Rz^!(\gamma_{p_c,\Lambda_B})$
followed by the composition isomorphism, which is the stated
compatibility with the affine-space purity comparison.
