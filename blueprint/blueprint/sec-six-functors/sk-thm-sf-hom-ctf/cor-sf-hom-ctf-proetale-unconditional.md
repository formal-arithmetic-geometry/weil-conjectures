+++
id = "cor-sf-hom-ctf-proetale-unconditional"
kind = "theorem"
title = "The pro-'etale internal Hom for a site-perfect first variable"
order = 2200
tags = ["latex:corollary"]
uses = ["lem-sf-comparison-tor-amplitude", "thm-sf-hom-comparison-constructible", "thm-sf-hom-ctf"]
+++
Let $K',M'\in D^b_{ctf}(X_{\Et},A)$ have Tor amplitude $[a,b]$
and $[c,d]$, and assume $K'$ is site-perfect. Then
$R\mathcal Hom_A(\nu_X^*K',\nu_X^*M')$ is bounded constructible
with Tor amplitude in $[c-b,d-a]$.

## Proof

Apply [thm-sf-hom-ctf] on the étale site, identify its pullback
by [thm-sf-hom-comparison-constructible], and transport the Tor
bound by [lem-sf-comparison-tor-amplitude].
