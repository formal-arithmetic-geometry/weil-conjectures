+++
id = "thm-galois-abstract-equivalence"
kind = "theorem"
title = "The abstract equivalence theorem"
order = 973
uses = ["def-galois-category", "lem-galois-action-continuous", "lem-galois-aut-profinite", "lem-galois-axioms", "lem-galois-object-exists", "lem-galois-transitive"]
+++
Let $(\mathcal C,F)$ be a Galois category and
$G=\operatorname{Aut}(F)$. Then $\mathcal C\to \text{finite-}G\text{-}\mathbf{Sets}$, $X\mapsto F(X)$ with the induced
$G$-action, is an equivalence of categories.

## Proof

Let $(\mathcal C,F)$ be a Galois category in the sense of
[def-galois-category] and $G=\operatorname{Aut}(F)$, profinite by
[lem-galois-aut-profinite].
The functor is well defined: each $F(X)$ is finite, and the action of
$G$ on it is continuous by [lem-galois-action-continuous], so $F(X)$ is a
finite continuous $G$-set; morphisms go to $G$-equivariant maps by
naturality.
Step 1: faithfulness is [lem-galois-axioms](1).
Step 2: full faithfulness. Let $s:F(X)\to F(Y)$ be $G$-equivariant. Its
graph $\Gamma_s\subseteq F(X)\times F(Y)=F(X\times Y)$ is a union of
connected components: $G$ acts transitively on the fibre of a connected
component by [lem-galois-transitive], so a $G$-equivariant subset is
a union of such fibres. Hence there is a union of connected components
$Z\subseteq X\times Y$ with $F(Z)=\Gamma_s$. The projection
$F(Z)\to F(X)$ is bijective, so $Z\to X$ is an isomorphism by axiom (4),
and $s=F(f)$ for the composite $f:X\to Z\to Y$. Together with Step 1
this makes $F$ fully faithful.
Step 3: essential surjectivity. It suffices to realize $G/H$ for $H$
open of finite index. By definition of the topology on $G\le \prod_X\operatorname{Aut}(F(X))$ there are finitely many objects $X_i$,
which we may take connected, with
$\ker\bigl(G\to\prod_i\operatorname{Aut}(F(X_i))\bigr)\subseteq H$.
Choose a Galois object $Y$ mapping to a connected component of
$\prod_iX_i$ ([lem-galois-object-exists]) and identify
$F(Y)=G/U$ for the open subgroup $U$ fixing a chosen element; since
$Y$ is Galois, $U$ is normal. As $F(Y)\to F(X_i)$ is surjective,
$U\subseteq H$. Let $M\subseteq\operatorname{Aut}(Y)$ correspond to
$(H/U)^{\mathrm{op}}\subseteq(G/U)^{\mathrm{op}} =\operatorname{Aut}(Y)$, and put $X=Y/M$, the coequalizer of the maps
$m:Y\to Y$, $m\in M$. Exactness of $F$ gives
$F(X)=F(Y)/M=G/H$, as required.
