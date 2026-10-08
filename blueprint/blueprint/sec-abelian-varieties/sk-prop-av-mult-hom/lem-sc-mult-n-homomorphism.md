+++
id = "lem-sc-mult-n-homomorphism"
kind = "lemma"
title = "Multiplication by $n$ is a homomorphism"
lean = ["AlgebraicGeometry.isMonHom_npow_id"]
order = 494
uses = ["def-sc-group-scheme"]
+++
Let $G$ be a commutative group scheme
over a field $k$, with multiplication $m$, inverse $i$, unit $e$
and structure morphism $p:G\to\Spec k$. Define
$[0]:=e\circ p:G\to G$ and, inductively,
$[n+1]:=m\circ([n],\mathrm{id}_G):G\to G$. Then for all
$n,m\geq0$:

1. **(a)** $[n]$ is a homomorphism of group schemes and
$[n](R)(x)=nx$ for every $k$-algebra $R$ and $x\in G(R)$;
1. **(b)** $m\circ([n],[m])=[n+m]$ and $[n]\circ[m]=[nm]$;
1. **(c)** $[n]\circ e=e$ and $[n]\circ i=i\circ[n]$.

## Proof

We work on $R$-points, where the functor of points is faithful
([def-sc-group-scheme]); write $\cdot$ for the group law of
$G(R)$ and $e$ for its unit.

(a) By induction on $n$ one has $[n](R)(x)=x\cdot\ldots\cdot x$
($n$ factors): this holds for $n=0$ by the definition of $[0]$, for
$n=1$ because $[1]=m\circ(e\circ p,\mathrm{id}_G)$ is the identity,
and in general because $[n+1](R)(x)=[n](R)(x)\cdot x$. The map
$x\mapsto x\cdot\ldots\cdot x$ is a homomorphism of groups because
$G(R)$ is commutative, and $[n]$ is a morphism of schemes by
construction; hence $[n]$ is a homomorphism of group schemes in the
sense of [def-sc-group-scheme].

(b) Both identities follow from (a) on $R$-points:
$[n](x)\cdot[m](x)=(n+m)x=[n+m](x)$ and
$[n]([m](x))=n(mx)=(nm)x=[nm](x)$.

(c) $[n](R)(e)=ne=e$ and
$[n](R)(i(x))=n(-x)=-(nx)=i([n](R)(x))$, again by (a).
