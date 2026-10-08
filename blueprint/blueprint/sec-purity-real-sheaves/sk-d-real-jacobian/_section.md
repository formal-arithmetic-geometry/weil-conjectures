+++
id = "sk-d-real-jacobian"
kind = "section"
title = "Jacobian torsion data and Kummer coefficients"
order = 2606
uses = ["sk-d-real-cohom", "sk-d-real-setup", "sk-def-av-jacobian", "sk-def-av-pic"]
lean = ["AlgebraicGeometry.JacobianTorsionDatum", "AlgebraicGeometry.JacobianTorsionDatum.tateModule"]
+++
*Definition (sketch).*

For a proper smooth geometrically connected curve $C_0/\Fq$, write
$C=C_0\times_{\Fq}k$ using geometric base change.
The group $\operatorname{Pic}(C)$ consists of line bundles up to
isomorphism, with tensor product as addition. A Jacobian torsion datum
is an abelian variety $J_0/\Fq$ (a smooth proper geometrically connected
commutative group scheme) with Galois-equivariant isomorphisms

$$
J[\ell^n]\simeq\operatorname{Pic}(C)[\ell^n],\qquad
J[\ell^n]=\ker(\ell^n:J_0(k)\to J_0(k)),
$$

compatible with multiplication by $\ell$ and tensor power by $\ell$.
Put $T_\ell J=\varprojlim_nJ[\ell^n]$ and $V_\ell J=T_\ell J\otimes\Ql$.
The etale sheaf $\mathbf G_m$ is the sheaf of units, and
$\mu_m=\ker(u\mapsto u^m)$.
The roots-of-unity system $(\mu_{\ell^n},z\mapsto z^\ell)$ defines
$\mathbf Z_\ell(1)$; invert $\ell$ and extend coefficients to obtain
$E(1)$. Geometric Frobenius acts on this line by $q^{-1}$, agreeing
with the cohomological Tate convention.

Uses: [sk-d-real-cohom], [sk-d-real-setup]
