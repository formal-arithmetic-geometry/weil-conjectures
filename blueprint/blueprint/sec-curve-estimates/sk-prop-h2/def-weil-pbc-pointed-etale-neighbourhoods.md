+++
id = "def-weil-pbc-pointed-etale-neighbourhoods"
kind = "definition"
title = "Pointed etale neighbourhood category"
order = 942
uses = ["def-weil-pbc-etale-site", "def-weil-pbc-scheme-conventions"]
+++
Let $\bar s:\operatorname{Spec}\Omega\to S$ be a geometric point. Define
$\mathcal N_{\bar s}$ to have objects pairs $(V,\bar v)$ with $V\to S$
etale and $\bar v:\operatorname{Spec}\Omega\to V$ above $\bar s$.
A morphism $(V,\bar v)\to(W,\bar w)$ is an $S$-map $V\to W$ carrying
$\bar v$ to $\bar w$. We index stalk colimits by
$\mathcal N_{\bar s}^{\mathrm{op}}$ so that restriction maps point forward.

## Detailed form

For a geometric point [def-weil-pbc-scheme-conventions] $\bar
s:\operatorname{Spec}\Omega\to S$, let $\mathcal N_{\bar s}$ be the category
whose objects are pairs $(V,\bar v)$ with $V\to S$ etale
[def-weil-pbc-scheme-conventions] and $\bar v\to V$ above $\bar s$. A
morphism preserves the chosen geometric points. Stalk colimits are indexed by
$\mathcal N_{\bar s}^{\mathrm{op}}$.
