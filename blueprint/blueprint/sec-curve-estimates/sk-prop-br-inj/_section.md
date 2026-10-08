+++
id = "sk-prop-br-inj"
kind = "section"
title = "Generic-point injection for the Brauer group"
order = 900
uses = ["sk-def-br", "sk-prop-divisor-gen", "sk-prop-hilbert90"]
lean = ["AlgebraicGeometry.Scheme.injective_cohomologyMap_gmSheaf_two"]
+++
*Proposition (sketch).*

Let $X$ be as in [sk-prop-divisor-gen] with function field
$k(X)$. Then (Grothendieck's residue sequence) the base change map
is injective:

$$
\Br(X)=H^2(X,\mathbb G_m)\hookrightarrow
H^2(\eta,\mathbb G_m)=\Br(k(X)).
$$

In particular this holds for $C$ a smooth curve.

## Proof

Take the long exact cohomology sequence of [sk-prop-divisor-gen].
The third term is a direct sum of the sheaves $i_{x*}\Z$, and
$H^1\big(X,i_{x*}\Z\big)=0$ for each $x$: in low degrees the Leray
spectral sequence for $i_x$ reduces this to
$H^1(\kappa(x),\Z)=\mathrm{Hom}_{\mathrm{cont}}(\mathrm{Gal} (\kappa(x)^{\mathrm{sep}}/\kappa(x)),\Z)$, which vanishes because a
continuous homomorphism from a profinite group to the discrete
torsion-free group $\Z$ has finite — hence trivial — image.
Cohomology commutes with the direct sum here: $X$ is noetherian, hence
quasi-compact and quasi-separated, so étale cohomology on $X$ commutes
with filtered colimits of abelian sheaves, and the direct sum is the
filtered colimit of its finite partial sums. Hence

$$
0=H^1\Big(X,\bigoplus_xi_{x*}\Z\Big)\to H^2(X,\mathbb G_m)
\to H^2(X,i_*\mathbb G_{m,\eta})
$$

is exact, so $H^2(X,\mathbb G_m)\hookrightarrow H^2(X,i_*\mathbb G_{m,\eta})$. Next, $R^1i_*\mathbb G_{m,\eta}=0$:
its stalk at a geometric point $\bar x$ over $x\in X$ is
$H^1(\Spec(A\otimes_{\mathcal O_{X,x}}k(X)),\mathbb G_m)
=\Pic(A\otimes_{\mathcal O_{X,x}}k(X))$ by Hilbert 90
([sk-prop-hilbert90]), where $A=\mathcal O^{\mathrm{sh}}_{X,\bar x}$
is a regular local ring, hence a UFD, and a localization of a UFD is
a UFD, whose Picard group is trivial. In the Leray spectral sequence
$E_2^{a,b}=H^a(X,R^bi_*\mathbb G_{m,\eta})\Rightarrow
H^{a+b}(\eta,\mathbb G_m)$ the only differential into $E_2^{2,0}$
comes from $E_2^{0,1}=H^0(X,R^1i_*\mathbb G_{m,\eta})=0$, so the edge
map $H^2(X,i_*\mathbb G_{m,\eta})\to H^2(\eta,\mathbb G_m)=\Br(k(X))$
is injective, and the composite is the claimed injection. (We do
*not* assert $H^2(X,i_*\mathbb G_{m,\eta})=\Br(k(X))$ or
$R^2i_*\mathbb G_{m,\eta}=0$: both fail for
$X=\Spec\mathbf C[[x,y]]$, where $H^2(X,i_*\mathbb G_{m,\eta})=0$
because $X$ is strictly local (Stacks `03QO`) while
$\Br(\mathbf C((x,y)))$ contains the quaternion class $(x,y)$,
detected by its $x$-adic residue.) (In degrees $0$ and $1$ the same
sequence gives $H^0(X,\mathbb G_m)=k^\times$ for $X$ proper
connected over algebraically closed $k$ and
$H^1(X,\mathbb G_m)=\Pic(X)=\mathrm{Div}(X)/\mathrm{Princ}(X)$,
which is (P1) of [sk-def-pic].)

Uses: [sk-def-br], [sk-prop-divisor-gen], [sk-prop-hilbert90]
