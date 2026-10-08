+++
id = "lem-wf-conjugation-geometric-monodromy"
kind = "lemma"
title = "Conjugation preserves the geometric monodromy group"
order = 2502
uses = ["def-wf-fundamental-representation", "def-wf-geometric-monodromy-group", "def-wf-weil-group", "lem-wf-weil-fundamental-representation", "lem-wf-zariski-closure-subgroup"]
+++
Let $X_0$ be a geometrically connected separated finite-type
$k_0$-scheme, let
$\rho:W(X_0)\to\operatorname{GL}(V)$ be the Weil fundamental
representation of [def-wf-fundamental-representation] attached to a
lisse Weil sheaf, let $H_{\mathrm{geom}}$ be the
geometric monodromy group of
[def-wf-geometric-monodromy-group], and let $s\in W(X_0)$ have
degree one in the sense of [def-wf-weil-group]. Then

$$
\alpha(h):=\rho(s)h\rho(s)^{-1}
$$

maps $H_{\mathrm{geom}}$ onto itself and is an automorphism of the
algebraic group $H_{\mathrm{geom}}$.

## Proof

The geometric subgroup $\pi_1(X)$ is the kernel of the degree
homomorphism of [def-wf-weil-group], hence normal in $W(X_0)$;
therefore the set $\rho(\pi_1(X))$ is carried onto itself by
conjugation with $\rho(s)$, because $\rho$ is a homomorphism by
[lem-wf-weil-fundamental-representation] of the representation of
[def-wf-fundamental-representation]. Conjugation by the matrix
$\rho(s)$ is a homeomorphism of $\operatorname{GL}(V)$ for the Zariski
topology, so it carries the closure
$H_{\mathrm{geom}}=\overline{\rho(\pi_1(X))}^{\mathrm{Zar}}$ of
[def-wf-geometric-monodromy-group] onto
$\overline{\rho(s)\rho(\pi_1(X))\rho(s)^{-1}}^{\mathrm{Zar}} =H_{\mathrm{geom}}$. The set $H_{\mathrm{geom}}$ is a subgroup by
[lem-wf-zariski-closure-subgroup], and conjugation is a group
homomorphism, so $\alpha$ is an automorphism of the group
$H_{\mathrm{geom}}$; as a conjugation inside the algebraic group
$\operatorname{GL}(V)$ it is a morphism of varieties, hence an
automorphism of algebraic groups.
