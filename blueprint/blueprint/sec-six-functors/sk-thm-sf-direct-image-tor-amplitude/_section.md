+++
id = "sk-thm-sf-direct-image-tor-amplitude"
kind = "section"
title = "Direct image with finite Tor amplitude"
order = 2190
uses = ["sk-lem-sf-flat-model", "sk-prop-sf-finiteness"]
lean = ["AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar", "AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar"]
+++
*Theorem (sketch).*

Let $A=A_{E,n}$ be a finite coefficient stage, let $f:X\to Y$ be separated
of finite type, of finite-type $k$-schemes with
$\dim X\le d$, and let $K$ be a bounded constructible $A$-complex on
$X_{\Et}$ with finite Tor amplitude in $[a,b]$. Then $Rf_*K$ is bounded
constructible on $Y_{\Et}$ with finite Tor amplitude in $[a,b+2d]$.

## Proof

Take the bounded flat model $P$ of [sk-lem-sf-flat-model], so
$\mathcal H^q(K)=0$ outside $[a,b]$. Let $\kappa=A/(\varpi_E)$; the
truncation spectral sequence for the left exact direct image applied to
$K\otimes^L_A\kappa_X$ has
$E_2^{p,q}=R^pf_*\bigl(\mathcal H^q(K\otimes^L_A\kappa_X)\bigr)$ with
$q\in[a,b]$ and $p\le 2d$ by the uniform vanishing of $R^pf_*$ above
$2\dim X$ on *every* module sheaf, which is
thm:sc-finite-type-torsion-cd ([sk-prop-sf-finiteness]); hence
$\mathcal H^n(Rf_*(K\otimes^L_A\kappa_X))=0$ outside $[a,b+2d]$.
Constructibility of $Rf_*K$ is prop:sf-finiteness. The canonical map
$(Rf_*K)\otimes^L_A\kappa_Y\to Rf_*(K\otimes^L_A\kappa_X)$ is an isomorphism
by a way-out argument that uses only the finite cohomological dimension of
$Rf_*$ (lem:sf-projection-finite-constant); the compact-support
projection formula of [sk-rem-sf-pf-done] concerns $Rf_!$ and does not
apply to a non-proper $f$, and $\kappa$ is not a perfect $A$-module when
$n>1$, so neither gives this directly. Explicitly: choose a resolution
$F_\bullet\to\kappa$ by finite free $A$-modules ($A$ is Noetherian); $Rf_*$
commutes with finite direct sums and with cones, hence with
$-\otimes_A\sigma_{\ge-m}F_\bullet$ for every stupid truncation; the cones
$K\otimes_A\sigma_{<-m}F_\bullet$ and $(Rf_*K)\otimes_A\sigma_{<-m}F_\bullet$
lie in degrees $\le b-m-1$ and $\le b+2d-m-1$, and $Rf_*$ raises degrees by
at most $2d$ by the uniform vanishing above; so for each degree $r$ both
sides agree in degree $r$ once $m\gg r$. The residue
test lem:exc-residue-tor-test converts the concentration of
$Rf_*(K\otimes^L_A\kappa_X)$ in $[a,b+2d]$ into finite Tor
amplitude of $Rf_*K$ in $[a,b+2d]$.

Uses: `\Cref{lem-sf-flat-model}`, `\Cref{sk-prop-sf-finiteness}`, `lem-exc-residue-tor-test`, `thm-sc-finite-type-torsion-cd`, `lem-sf-projection-finite-constant`
