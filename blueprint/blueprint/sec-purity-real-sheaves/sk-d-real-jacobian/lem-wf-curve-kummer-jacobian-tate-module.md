+++
id = "lem-wf-curve-kummer-jacobian-tate-module"
kind = "lemma"
title = "Kummer identifies curve cohomology with the Jacobian Tate module"
order = 2610
uses = ["def-coefficient-twists-detailed", "def-sc-jacobian", "def-sc-kummer-sequence", "def-sc-pic0", "def-wf-abelian-tate-module", "lem-sc-global-functions", "lem-sc-h1-gm-pic", "lem-sc-kummer-exact", "lem-wf-geometric-jacobian-galois-action", "thm-sc-jacobian-representability"]
+++
Let $C_0/k_0$ be a smooth projective geometrically connected curve, put
$C=C_0\times_{k_0}\overline{k}_0$, and let $J$ be its
Jacobian, equipped with the canonical semilinear
$\operatorname{Gal}(\overline{k}_0/k_0)$-action of
[lem-wf-geometric-jacobian-galois-action]. For
$\ell\ne\operatorname{char}k_0$, the
Kummer twist gives natural
Galois-equivariant isomorphisms

$$
H^1(C,A_n(1))\xrightarrow{\sim}J[\ell^n](\overline{k}_0).
$$

Here $A_n=\mathbf Z/\ell^n\mathbf Z$, and these isomorphisms are
compatible with the transition maps.
The Jacobian, Tate module, and twist in this display are those of
[def-sc-jacobian], [def-wf-abelian-tate-module], [def-coefficient-twists-detailed].

## Proof

For every $n\geq1$, the Kummer sequence of
[def-sc-kummer-sequence] with exponent $\ell^n$ is

$$
1\longrightarrow\mu_{\ell^n}\longrightarrow\mathbf G_m
\xrightarrow{(\cdot)^{\ell^n}}\mathbf G_m\longrightarrow1.
$$

It is exact by [lem-sc-kummer-exact]. The relevant beginning of its
long exact cohomology sequence is

$$
H^0(C,\mathbf G_m)\xrightarrow{\ell^n}H^0(C,\mathbf G_m)
\longrightarrow H^1(C,\mu_{\ell^n})
\longrightarrow H^1(C,\mathbf G_m)
\xrightarrow{\ell^n}H^1(C,\mathbf G_m).
$$

By [lem-sc-global-functions],
$H^0(C,\mathbf G_m)=\overline{k}_0^\times$, and the first arrow is
surjective because $\overline{k}_0$ is algebraically closed. The
identification $H^1(C,\mathbf G_m)=\operatorname{Pic}(C)$ of
[lem-sc-h1-gm-pic] therefore gives

$$
H^1(C,\mu_{\ell^n})\xrightarrow{\sim}
\operatorname{Pic}(C)[\ell^n].
\tag{1}
$$

If $L^{\otimes\ell^n}\cong\mathcal O_C$, then
$\ell^n\deg L=0$ in $\mathbf Z$, hence $\deg L=0$. By the
degree-zero definition in [def-sc-pic0], the right side of $(1)$ is
therefore $\operatorname{Pic}^0(C)[\ell^n]$. Since $J$ is the Jacobian of
the smooth projective curve $C$ over the separably closed field
$\overline{k}_0$, its points are the degree-zero invertible modules on
$C$, so
[thm-sc-jacobian-representability] identifies this group with
$J[\ell^n](\overline{k}_0)$; the identification is induced by the
representing isomorphism and is therefore canonical, hence equivariant for the
semilinear action of [lem-wf-geometric-jacobian-galois-action].

The transition map on the Kummer side is induced by
$\mu_{\ell^{n+1}}\to\mu_{\ell^n}$, $z\mapsto z^\ell$; under $(1)$ it
is multiplication by $\ell$ on the torsion of the Jacobian. Thus the
finite-level isomorphisms form the compatible inverse system defining
$T_\ell J$ in [def-wf-abelian-tate-module]; no separate
$\mathbf Z_\ell$-sheaf comparison is being assumed.
All arrows in the Kummer sequence, the connecting map to the Picard group,
and the identification of the Jacobian are natural under automorphisms
of $\overline{k}_0/k_0$, the last one by
[lem-wf-geometric-jacobian-galois-action]; hence the isomorphism is
Galois equivariant.
The displayed finite-level identifications are compatible with reduction;
whenever rational or $E$-coefficients are used below, they mean the
corresponding scalar extension of this compatible system.
