+++
id = "lem-trf-iterated-weil-cocycle"
kind = "lemma"
title = "Cocycle identity for the iterated Weil isomorphism"
order = 2297
uses = ["def-trf-iterated-weil-map", "def-trf-scheme-frobenius", "def-trf-strict-weil-complex"]
+++
Let $(K,\varphi)\in D^b_{ctf,\mathrm W}(X,A)$ be a
strict Weil complex under the
conventions of [def-trf-strict-weil-complex], with
$g_\gamma=g_X$ the
geometric-Frobenius automorphism
of [def-trf-scheme-frobenius], and let

$$
\varphi^{[m]}:Lg_\gamma^{m*}K\xrightarrow{\ \sim\ }K
\qquad(m\in\mathbf Z_{\geq1})
$$

be the iterated Weil isomorphism
of [def-trf-iterated-weil-map]. Then for all
$m,n\in\mathbf Z_{\geq1}$ the identity

$$
\varphi^{[m+n]}=\varphi^{[m]}\circ Lg_\gamma^{m*}\varphi^{[n]}
$$

holds after the canonical pullback identifications
$Lg_\gamma^{m*}Lg_\gamma^{n*}K\cong L(g_\gamma^m\circ g_\gamma^n)^*K=Lg_\gamma^{m+n*}K$.

## Proof

By [def-trf-strict-weil-complex], $\varphi$ is an isomorphism
$Lg_\gamma^*K\to K$ with $K\in D^b_{ctf}(X,A)$; by
[def-trf-scheme-frobenius], $g_\gamma$ is an automorphism of
$X$ satisfying $g_\gamma^{m+n}=g_\gamma^m\circ g_\gamma^n$, so that
the derived pullbacks satisfy $Lg_\gamma^{m+n*}\cong Lg_\gamma^{m*}Lg_\gamma^{n*}$ under the canonical identification
displayed in the statement. Under this identification both sides of
the identity are the composite of the $m+n$ maps

$$
Lg_\gamma^{m+n*}K\xrightarrow{Lg_\gamma^{m+n-1*}\varphi}\cdots
\xrightarrow{Lg_\gamma^*\varphi}K
$$

of [def-trf-strict-weil-complex]: the left-hand side is the
composite defining $\varphi^{[m+n]}$ in
[def-trf-iterated-weil-map], while the right-hand side is the
concatenation of the composites defining $\varphi^{[m]}$ and
$\varphi^{[n]}$ in [def-trf-iterated-weil-map]; the
concatenation is identified with the composite of the $m+n$ maps by
the associativity of composition and the naturality of the canonical
pullback identifications.
