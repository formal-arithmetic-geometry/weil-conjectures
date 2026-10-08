+++
id = "lem-sp-right-adjoint-preserves-injectives"
kind = "lemma"
title = "Right adjoints of exact functors preserve injectives"
order = 602
uses = ["def-sp-abelian", "def-sp-injective-resolutions"]
+++
Let $u:\mathcal A\to\mathcal B$ be an exact functor between abelian
categories [def-sp-abelian] admitting a right adjoint $u_*:\mathcal
B\to\mathcal A$. Then $u_*$ sends injective
[def-sp-injective-resolutions] objects to injective objects.

## Proof

By [def-sp-injective-resolutions], $I\in\mathcal B$ is injective iff for
every monomorphism $N\hookrightarrow N'$ in $\mathcal B$ the map

$$
 \operatorname{Hom}_{\mathcal B}(N',I)\longrightarrow
 \operatorname{Hom}_{\mathcal B}(N,I)
$$

is surjective. By the adjunction

$$
 \operatorname{Hom}_{\mathcal B}(uM,N)\cong
 \operatorname{Hom}_{\mathcal A}(M,u_*N),
$$

the injectivity of $u_*I$ is equivalent to the surjectivity of
$\operatorname{Hom}(uM',I)\to\operatorname{Hom}(uM,I)$ for every monomorphism
$M\hookrightarrow M'$ in $\mathcal A$; this holds because $u$ is exact, hence
preserves monomorphisms, and $I$ is injective.
