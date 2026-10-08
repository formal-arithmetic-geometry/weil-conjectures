+++
id = "lem-pur-cfiber-stalk"
kind = "lemma"
title = "Stalk of the compactly supported direct image"
order = 1984
uses = ["cor-weil-pbc-geometric-fiber-finite", "def-compact-support-direct-image-detailed", "def-pur-conventions", "def-weil-pbc-etale-origin-witness", "def-weil-pbc-geometric-stalks", "def-weil-scheme-morphism-properties", "thm-cbc-finite-level-proetale"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $\pi:E\to B$ be a
separated finite-type
morphism, let $K\in D^b_{ctf}(E,\Lambda)$, and let
$\bar b\to B$ be a geometric
point with the fiber $E_{\bar b}$. The canonical comparison

$$
(R\pi_!K)_{\bar b}\;\xrightarrow{\ \sim\ }\;R\Gamma_c(E_{\bar b},K|_{E_{\bar b}})
$$

is an isomorphism.

## Proof

The stalk is the filtered-neighborhood fiber of [def-weil-pbc-geometric-stalks].
Choose a compactification $c=(j,p)$ of $\pi$
([def-compact-support-direct-image-detailed]); its base change at
$\bar b$ is a compactification of $E_{\bar b}\to\bar b$. The
compatibility of geometric stalks with extension by zero and with the
proper direct image ([thm-cbc-finite-level-proetale] for the
compact-support functors, [cor-weil-pbc-geometric-fiber-finite]
for the proper direct image of the [def-weil-pbc-etale-origin-witness]
representative) gives the displayed comparison, the witnesses being
compatible by [def-compact-support-direct-image-detailed].
