+++
id = "sk-def-av-pic"
kind = "section"
title = "$\\Pic$, degree, $\\Pic^0$"
lean = ["AlgebraicGeometry.Scheme.Pic", "AlgebraicGeometry.Scheme.Hom.picZero"]
order = 440
uses = ["sec-nagata-compactification", "sk-def-curve"]
+++
*Definition (sketch).*

Let $C$ be a smooth projective geometrically integral curve over a
field $k$. We write $\Pic(C)=H^1(C_{\Et},\gm)$ for the group of
invertible $\cO_C$-modules up to isomorphism; there is a
*degree* homomorphism $\deg:\Pic(C)\to\Z$, and
$\Pic^0(C):=\ker(\deg)$. For a field extension $K/k$ we write
$C_K=C\times_kK$ and $\Pic^0(C_K)$ for the degree-zero part over $K$.
