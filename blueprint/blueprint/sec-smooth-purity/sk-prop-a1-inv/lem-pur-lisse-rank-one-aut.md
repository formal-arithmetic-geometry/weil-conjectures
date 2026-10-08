+++
id = "lem-pur-lisse-rank-one-aut"
kind = "lemma"
title = "Automorphisms of a rank-one finite locally constant sheaf"
order = 1959
uses = ["def-pur-conventions", "def-weil-derived-pullback-tensor-hom", "def-weil-scheme-morphism-properties"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $T$ be a separated
finite-type $k$-scheme and let $L,M$ be finite locally constant
$\Lambda$-sheaves of rank one on $T$.

1. The canonical map $\Lambda_T\to\mathcal Hom(L,L)$,
$1\mapsto\operatorname{id}_L$, is an isomorphism; hence every
endomorphism of $L$ is multiplication by a unique locally
constant function $T\to\Lambda$, and
$\operatorname{Aut}(L)=\Gamma(T,\Lambda_T^\times)$ is the group
of locally constant units.
1. Any two isomorphisms $\varphi,\psi:L\to M$ differ by a unique
automorphism of $M$: there is a unique locally constant unit
$u\in\Gamma(T,\Lambda_T^\times)$ with $\psi=u\cdot\varphi$.
In particular, for every geometric point $\bar t$ of $T$ and
every unit $v\in\Lambda^\times$ there is an isomorphism
$\psi:L\to M$ with $\psi_{\bar t}=v\cdot\varphi_{\bar t}$,
namely $\psi=v\cdot\varphi$ for the constant unit $v$.

## Proof

Step 1: (1). By [def-weil-scheme-morphism-properties] local
constancy means that $L$ becomes constant after pullback along a
covering family of the site; let $u:U\to T$ be a member of such a
family, so that $Lu^*L\cong\Lambda_U$. Pullback commutes with the
internal Hom of [def-weil-derived-pullback-tensor-hom], so it
carries the
canonical map $\Lambda_T\to\mathcal Hom(L,L)$ to the canonical map
$\Lambda_U\to\mathcal Hom(\Lambda_U,\Lambda_U)=\Lambda_U$, which is
an isomorphism; a morphism of sheaves which becomes an isomorphism
after pullback along a covering family is itself an isomorphism, by the
sheaf axiom. Hence $\Lambda_T\to\mathcal Hom(L,L)$ is an
isomorphism, and taking global sections writes
$\operatorname{End}(L)=\Gamma(T,\Lambda_T)$ as the ring of locally
constant $\Lambda$-valued functions, whose unit group is
$\Gamma(T,\Lambda_T^\times)$.
Step 2: (2). The composite $\psi\circ\varphi^{-1}$ is an
automorphism of $M$, hence is multiplication by a unique locally
constant unit $u$ by (1) applied to $M$; then
$\psi=u\cdot\varphi$, and conversely $u\cdot\varphi$ is an
isomorphism exactly for a unit $u$. For the final assertion take the
constant function with value $v\in\Lambda^\times$, which is a unit.
