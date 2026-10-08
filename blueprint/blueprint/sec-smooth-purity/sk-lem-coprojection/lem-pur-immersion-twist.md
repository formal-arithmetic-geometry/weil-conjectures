+++
id = "lem-pur-immersion-twist"
kind = "lemma"
title = "The co-projection for the twist"
order = 2007
uses = ["def-coefficient-twists-detailed", "def-pur-conventions", "def-weil-derived-tensor", "def-weil-exceptional-inverse-image", "def-weil-scheme-morphism-properties", "lem-pur-coprojection"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $i:Z\hookrightarrow X$ be a closed immersion of
separated finite-type
$k$-schemes and let $K\in D^b_{ctf}(X,\Lambda)$. Then, for
$m\in\mathbf Z$,

$$
Ri^!\bigl(K\otimes^L_{\Lambda_X}\Lambda_X(m)[2m]\bigr)
\;\xrightarrow{\ \sim\ }\;
Ri^!K\otimes^L_{\Lambda_Z}\Lambda_Z(m)[2m]
$$

via [lem-pur-coprojection] with the
Tate twist object
$L=\Lambda_X(m)[2m]$ (an invertible object of
[def-weil-derived-tensor], whose restriction to $Z$ is
$\Lambda_Z(m)[2m]$ by the [def-coefficient-twists-detailed]
restriction compatibility).

## Proof

Apply [lem-pur-coprojection] to the object $K$ on $W=X$ and
the invertible object $L=\Lambda_X(m)[2m]$, and use the
[def-coefficient-twists-detailed] identification
$i^*\Lambda_X(m)=\Lambda_Z(m)$.
