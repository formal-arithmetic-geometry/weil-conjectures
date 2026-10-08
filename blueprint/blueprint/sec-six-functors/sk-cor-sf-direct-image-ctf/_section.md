+++
id = "sk-cor-sf-direct-image-ctf"
kind = "section"
title = "The direct image cell on the pro-étale site"
order = 2192
uses = ["sk-prop-sf-comparison", "sk-thm-sf-direct-image-tor-amplitude"]
+++
*Corollary (sketch).*

For $f$ separated of finite type with $\dim X\le d$, $Rf_*$ carries
$\Dctf(X_{\Proet},A)$ into $\Dctf(Y_{\Proet},A)$, with finite Tor amplitude
$[a,b]\mapsto[a,b+2d]$; no restriction to objects of étale origin is needed.

## Proof

Every bounded constructible pro-étale coefficient complex is of étale
origin (09AK), so $K\cong\nu_X^*K'$; since $\nu_X^*$ is exact and
monoidal it transfers the finite Tor condition across the comparison in both
directions;
[sk-thm-sf-direct-image-tor-amplitude] gives the bound on the étale side;
and the comparison direct image of [sk-prop-sf-comparison] carries it
back.

Uses: `\Cref{sk-prop-sf-comparison}`, `\Cref{thm-sf-direct-image-tor-amplitude}`
