+++
id = "def-sc-genus"
kind = "definition"
title = "The genus of a curve"
lean = ["AlgebraicGeometry.Scheme.Hom.genus"]
order = 419
uses = ["def-sc-curves"]
+++
Let $C$ be a proper smooth connected curve over
an algebraically closed field $k$. The *genus* of $C$ is

$$
g(C):=\dim_kH^1(C,\mathcal O_C),
$$

finite because coherent cohomology of a proper scheme over a field
is finite-dimensional (coherent higher direct images of a proper
morphism are coherent: *reference: Stacks Project, Cohomology
of Schemes, Proposition 30.19.1, [Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)*; this is the genus of
Stacks Project, Algebraic Curves, Definition 53.8.1,
[Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7), which
defines $g=\dim_kH^1(X,\mathcal O_X)$ for a proper scheme $X$ of
dimension one with $H^0(X,\mathcal O_X)=k$, the present $C$).
Equivalently, by duality
$g=\dim_kH^0(C,\Omega^1_{C/k})$ (*reference: Stacks Project,
Algebraic Curves, Lemma 53.4.1, [Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2), parts (5) and
(6)*). (For a smooth separated, not necessarily proper, connected curve the
genus used in this blueprint is the genus of a compactification
$\overline C$ of $C$, i.e. of a proper smooth connected curve containing
$C$ as an open subscheme with finite complement; this convention is
fixed explicitly at the single place where it is used, and it is the
compactification lemma below that provides the compactification.)
