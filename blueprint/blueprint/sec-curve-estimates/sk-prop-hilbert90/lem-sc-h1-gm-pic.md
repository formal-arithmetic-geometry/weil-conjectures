+++
id = "lem-sc-h1-gm-pic"
kind = "lemma"
title = "The Picard group as first cohomology of units"
order = 884
uses = ["def-sc-curves", "def-sc-gm-torsor", "def-sc-invertible-module", "def-sc-picard-group", "thm-sc-hilbert-90"]
+++
Let $C$ be a curve. There are
canonical isomorphisms of abelian groups

$$
\operatorname{Pic}(C)\xrightarrow{\ \sim\ }
H^1(C_{\mathrm{Zar}},\mathcal O_C^{\times})\xrightarrow{\ \sim\ }
H^1(C_{\Et},\mathbf G_m),
$$

the first sending the class of an
invertible module $\mathcal L$
to the Zariski $\mathcal O_C^{\times}$-torsor
$\underline{\operatorname{Isom}}(\mathcal O_C,\mathcal L)$, the second
being the natural comparison map (pull-back along the morphism of
sites $\varepsilon:C_{\Et}\to C_{\mathrm{Zar}}$, using
$\varepsilon^{-1}\mathcal O_C^{\times}\to\mathbf G_m$), and the
composite sending $\mathcal L$ to the etale torsor
$\underline{\operatorname{Isom}}(\mathcal O_C,\mathcal L)$. In particular
$H^1(C_{\Et},\mathbf G_m)\cong\operatorname{Pic}(C)\cong
H^1(C_{\mathrm{Zar}},\mathcal O_C^{\times})$.

## Proof

This is the case $X=C$ of [thm-sc-hilbert-90]. The group of
isomorphism classes of invertible $\mathcal O_C$-modules
([def-sc-invertible-module]) under $\otimes$ appearing there is
$\operatorname{Pic}(C)$ of [def-sc-picard-group] (same set, same group
law), and the three maps of the statement are the ones of
[thm-sc-hilbert-90] for $X=C$: $\mathcal L\mapsto[\underline{\operatorname{Isom}}(\mathcal O_C,\mathcal L)]$
into Zariski cohomology, the comparison map along
$\varepsilon:C_{\Et}\to C_{\mathrm{Zar}}$, and their composite
$\mathcal L\mapsto[\underline{\operatorname{Isom}}(\mathcal O_{C_{\Et}},\mathcal L_{\Et})]$.
(*Stacks Project, Lemma 21.6.1, Tag [040E](https://stacks.math.columbia.edu/tag/040E)*,
in Section 21.6: for a (locally) ringed site,
$H^1(\mathcal C,\mathcal O^*)=\operatorname{Pic}(\mathcal O)$.)
