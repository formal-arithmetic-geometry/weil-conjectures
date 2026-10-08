+++
id = "lem-galois-axioms"
kind = "lemma"
title = "Consequences of the axioms"
order = 970
uses = ["def-galois-category"]
+++
Let $(\mathcal C,F)$ be a Galois category. Then:

1. $F$ is faithful;
1. $X\to Y$ is a monomorphism if and only if $F(X)\to F(Y)$ is
injective, and an epimorphism if and only if $F(X)\to F(Y)$ is
surjective;
1. an object is initial if and only if its image under $F$ is empty,
and final if and only if its image is a singleton;
1. every morphism between connected objects is an epimorphism;
1. if $X$ is connected and $a,b:X\to Y$ agree on one element of
$F(X)$, then $a=b$;
1. for connected $X$ and $s\in F(X)$ the map
$\operatorname{Aut}(X)\to F(X)$, $g\mapsto F(g)(s)$, is injective, so
$\#\operatorname{Aut}(X)\le\#F(X)$; $X$ is *Galois* if equality
holds, equivalently if $\operatorname{Aut}(X)$ acts transitively on
$F(X)$;
1. if $X=\coprod_iX_i$ and $Y=\coprod_jY_j$ with connected $X_i$,
$Y_j$, then every morphism $X\to Y$ is given by a map of index sets
$\alpha$ with components $X_i\to Y_{\alpha(i)}$.

## Proof

(1) Throughout, $(\mathcal C,F)$ is a Galois category in the sense of
[def-galois-category] and the axioms referred to are those of that
definition. If $F(a)=F(b)$ for $a,b:X\to Y$, the equalizer $E\to X$ satisfies
$F(E)=F(X)$, so $E\to X$ is an isomorphism by axiom (4) and $a=b$.
(2) $X\to Y$ is a monomorphism iff $X\to X\times_YX$ is an
isomorphism; applying the exact functor $F$ turns this into
$F(X)\to F(X)\times_{F(Y)}F(X)$, which is an isomorphism iff
$F(X)\to F(Y)$ is injective, and axiom (4) transports the conclusion
back. Dually for epimorphisms, using $Y\amalg_XY\to Y$.
(3) The initial object has empty image; conversely if $F(X)=\emptyset$
the unique morphism from the initial object induces a bijection under $F$,
hence is an isomorphism by axiom (4). Dually for the final object.
(4) For a morphism $X\to Y$ of connected objects the image $Z\subseteq Y$, the equalizer of $Y\rightrightarrows Y\amalg_XY$, satisfies
$F(Z)\neq\emptyset$ because $F(X)\to F(Z)$ is surjective and
$F(X)\neq\emptyset$; hence $Z=Y$ by connectedness of $Y$.
(5) The equalizer $E\to X$ of $a,b$ is initial or all of $X$ by
connectedness, and $F(E)\subseteq F(X)$ is the set on which $F(a)$ and
$F(b)$ agree.
(6) Apply (5) to $a=g$, $b=\operatorname{id}_X$: if $F(g)(s)=s$ then
$g=\operatorname{id}_X$. Hence $g\mapsto F(g)(s)$ is injective and
$\#\operatorname{Aut}(X)\le\#F(X)$; if the action is transitive the map is
also surjective, so equality holds.
(7) For each $i,j$ the projection $E_{ij}=X_i\times_YY_j\to X_i$ is a
monomorphism, hence an isomorphism for exactly one $j$ (the one whose
$F(Y_j)$ meets the image of $F(X_i)\to F(Y)$) and has initial source for
all others, by connectedness of $X_i$.
