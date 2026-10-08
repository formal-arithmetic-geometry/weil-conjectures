+++
id = "def-weil-pbc-derived-exchange"
kind = "definition"
title = "Derived exchange map"
order = 1040
lean = ["AlgebraicGeometry.Etale.derivedBaseChangeMapPlus"]
uses = ["def-weil-pbc-cartesian-square", "def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "def-weil-pbc-inverse-image", "def-weil-pbc-kinjective-resolutions", "def-weil-pbc-underived-exchange"]
+++
For $K\in D^+(X_{\mathrm{et}})$ choose an injective resolution
$K\xrightarrow{\simeq}I^\bullet$. Apply
$\operatorname{Ex}_{\square,I^r}$ in every degree and use the naturality
lemma to obtain a morphism of complexes

$$
g^{-1}f_*I^\bullet\longrightarrow f'_*g'^{-1}I^\bullet.
$$

Choose a K-injective replacement
$g'^{-1}I^\bullet\xrightarrow{\simeq}J^\bullet$ in the Grothendieck
category of etale abelian sheaves on $X'$. Compose the displayed map with
$f'_*g'^{-1}I^\bullet\to f'_*J^\bullet$ and define

$$
\operatorname{Ex}_{\square,K}:g^{-1}f_*I^\bullet\longrightarrow f'_*J^\bullet
$$

to be its class in $D^+(Y'_{\mathrm{et}})$. The target complex is a model
for $Rf'_*g'^{-1}K$, since $J^\bullet$ is K-injective; the source is a model
for $g^{-1}Rf_*K$ because $g^{-1}$ is exact.
Its class in $D^+(Y'_{\mathrm{et}})$ is

$$
\operatorname{Ex}_{\square,K}:g^{-1}Rf_*K\longrightarrow
Rf'_*g'^{-1}K.
$$

## Detailed form

For $K\in\Dplus(X_{\Et})$, the *derived exchange morphism* is the adjoint
mate

$$
 \Ex_{\square,K}:g^{-1}Rf_*K\longrightarrow Rf'_*g'^{-1}K
$$

of the composite

$$
 f'^{-1}g^{-1}Rf_*K\xrightarrow{\theta_\square}
 g'^{-1}f^{-1}Rf_*K\xrightarrow{g'^{-1}\varepsilon_f}g'^{-1}K,
$$

using the derived adjunction of the inverse-image adjunction
[def-weil-pbc-inverse-image] and the specified isomorphism $\theta_\square$
of the cartesian square [def-weil-pbc-cartesian-square].
Equivalently, choose a K-injective resolution
[def-weil-pbc-kinjective-resolutions] $K\to I$, apply the underived exchange
morphism [def-weil-pbc-underived-exchange] $\Ex^0_{\square,I}$ term
by term, and compare $g'^{-1}I$ with a K-injective resolution on $X'$.
