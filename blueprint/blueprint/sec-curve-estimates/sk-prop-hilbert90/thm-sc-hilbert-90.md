+++
id = "thm-sc-hilbert-90"
kind = "theorem"
title = "Hilbert 90 for a scheme"
order = 882
uses = ["def-sc-gm-torsor", "def-sc-invertible-module", "lem-sc-line-bundle-torsor", "lem-sc-torsor-h1"]
+++
Let $X$ be a scheme (for instance a curve $C$ as in
[def-sc-curves]). The set of isomorphism classes of invertible
$\mathcal O_X$-modules ([def-sc-invertible-module]) is an
abelian group under $\otimes$, and the natural maps are isomorphisms
of abelian groups

$$
\{\text{invertible }\mathcal O_X\text{-modules}\}/{\cong}
\;\xrightarrow{\ \sim\ }\;
H^1(X_{\mathrm{Zar}},\mathcal O_X^\times)\;\xrightarrow{\ \sim\ }\;
H^1(X_{\Et},\mathbf G_m),
$$

the first sending $\mathcal L$ to the Zariski torsor
$\underline{\operatorname{Isom}}(\mathcal O_X,\mathcal L)$, the second
being the comparison map induced by the morphism of sites
$\varepsilon:X_{\Et}\to X_{\mathrm{Zar}}$ and
$\varepsilon^{-1}\mathcal O_X^{\times}\to\mathbf G_m$, and the
composite sending the class of $\mathcal L$ to the class of the
$\mathbf G_m$-torsor
$\underline{\operatorname{Isom}}(\mathcal O_{X_{\Et}},\mathcal L_{\Et})$.
(*Stacks Project, Tag [03P8](https://stacks.math.columbia.edu/tag/03P8)*.)

## Proof

*The two maps out of the Picard set are bijective group maps.* By
[lem-sc-torsor-h1], $H^1(X_{\Et},\mathbf G_m)$ is the group of
isomorphism classes of $\mathbf G_m$-torsors ([def-sc-gm-torsor])
under contracted product, and $H^1(X_{\mathrm{Zar}},\mathcal O_X^{\times})$
is likewise the group of Zariski $\mathcal O_X^{\times}$-torsors. By
[lem-sc-line-bundle-torsor] (etale and Zariski versions),
$\mathcal L\mapsto\underline{\operatorname{Isom}}(\mathcal O,\mathcal L)$
is in both cases a bijection from the set of isomorphism classes of
invertible modules, carrying $\otimes$ to contracted product and
$\mathcal O_X$ to the trivial torsor. Transporting the group structure,
$\otimes$ makes the Picard set an abelian group (with inverse the class
of the torsor inverse, i.e. of $\mathcal L^{\vee}$) and both maps are
group isomorphisms.

*The comparison map.* Under the torsor descriptions of
[lem-sc-torsor-h1], the comparison map
$H^1(X_{\mathrm{Zar}},\mathcal O_X^{\times})\to H^1(X_{\Et},\mathbf G_m)$
sends a Zariski torsor $T$ to the etale torsor
$\varepsilon^{-1}T\times^{\varepsilon^{-1}\mathcal O_X^{\times}}\mathbf G_m$:
indeed it is obtained from the extension
$0\to\mathcal O_X^{\times}\to E\to\mathbf Z_X\to0$ of $T$ by the exact
functor $\varepsilon^{-1}$ followed by push-out along
$\varepsilon^{-1}\mathcal O_X^{\times}\to\mathbf G_m$, and the preimage
of $1$ in the push-out is this contracted product. For
$T=\underline{\operatorname{Isom}}(\mathcal O_X,\mathcal L)$, the map
sending a Zariski-local isomorphism $\varphi:\mathcal O_U\to\mathcal L|_U$
and a unit $u$ on an etale $V\to U$ to the
$\mathcal O_{X_{\Et}}$-linear isomorphism $u\cdot\varphi_V$ of
$\mathcal O_V$ onto $\mathcal L_{\Et}|_V$ is a $\mathbf G_m$-equivariant
map from this torsor to
$\underline{\operatorname{Isom}}(\mathcal O_{X_{\Et}},\mathcal L_{\Et})$,
hence an isomorphism (an equivariant map of torsors is one, as one
checks locally). So the triangle formed by the three maps commutes;
since the two maps out of the Picard group are isomorphisms, so is the
comparison map.
