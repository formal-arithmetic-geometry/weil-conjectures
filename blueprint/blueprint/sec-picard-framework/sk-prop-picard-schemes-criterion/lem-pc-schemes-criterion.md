+++
id = "lem-pc-schemes-criterion"
kind = "lemma"
title = "A representability criterion via covers"
order = 777
uses = ["def-pc-representable-functor", "def-pc-subfunctor"]
lean = ["AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable"]
+++
(Schemes, Lemma 26.15.4, Tag
[01JJ](https://stacks.math.columbia.edu/tag/01JJ).) Let
$F:(\mathit{Sch}/S)^{\mathrm{op}}\to\textit{Sets}$ be a functor and suppose:

1. **(1)** $F$ satisfies the sheaf property for the Zariski topology;
1. **(2)(a)** there exists a family $(F_i)_{i\in I}$ of subfunctors of
$F$ each of which is representable;
1. **(2)(b)** each inclusion $F_i\subseteq F$ is
representable by open immersions;
1. **(2)(c)** the family $(F_i)_{i\in I}$ covers $F$.

Then $F$ is representable by a scheme over $S$.

## Proof

For $i\in I$ choose a scheme $X_i$ over $S$ representing $F_i$ and the
universal element $\xi_i\in F_i(X_i)\subseteq F(X_i)$, and let
$U_{ij}\subseteq X_i$ be the open subscheme given by (2)(b) for the
inclusion $F_j\subseteq F$: a morphism $T\to X_i$ factors through
$U_{ij}$ if and only if the pullback of $\xi_i$ to $T$ lies in
$F_j(T)$. In particular $\xi_i|_{U_{ij}}\in F_j(U_{ij})$, so by the
representability of $F_j$ the element $\xi_i|_{U_{ij}}$ comes from a
unique morphism

$$
\varphi_{ij}:U_{ij}\longrightarrow X_j
$$

with $\varphi_{ij}^*\xi_j=\xi_i|_{U_{ij}}$. The element
$\varphi_{ij}^*\xi_j=\xi_i|_{U_{ij}}$ of $F(U_{ij})$ lies in
$F_i(U_{ij})$, so by (2)(b) for the inclusion $F_i\subseteq F$ the
morphism $\varphi_{ij}$ factors through the largest open
$U_{ji}\subseteq X_j$ with $\xi_j|_{U_{ji}}\in F_i(U_{ji})$: we get
$\varphi_{ij}(U_{ij})\subseteq U_{ji}$, i.e. $\varphi_{ij}$ factors
as $U_{ij}\to U_{ji}\hookrightarrow X_j$. The
composite

$$
\varphi_{ji}\circ\varphi_{ij}:U_{ij}\longrightarrow U_{ji}\subseteq X_i
$$

pulls $\xi_i$ back to
$\varphi_{ij}^*\varphi_{ji}^*\xi_j=\varphi_{ij}^*\xi_j=\xi_i|_{U_{ij}}$
(here we used (2)(b) twice, i.e. that the two open embeddings
$U_{ji}\hookrightarrow X_j$ and $U_{ij}\hookrightarrow X_i$ respect
the elements), so by the uniqueness of the morphism representing
$\xi_i$ over $X_i$: $\varphi_{ji}\circ\varphi_{ij} =\mathrm{id}_{U_{ij}}$; similarly
$\varphi_{ij}\circ\varphi_{ji}=\mathrm{id}_{U_{ji}}$. Hence the
$\varphi_{ij}:U_{ij}\to U_{ji}$ are mutually inverse isomorphisms.

The compatibility condition of the classical glueing lemma for schemes
is the equality

$$
\varphi_{ij}^{-1}(U_{ji}\cap U_{jk})=U_{ij}\cap U_{ik} :
$$

both sides are the largest open $W\subseteq U_{ij}$ with
$\xi_i|_W\in F_k(W)$ (for the left: $U_{ji}\cap U_{jk}$ is the
largest open $V\subseteq U_{ji}$ with $\xi_j|_V\in F_k(V)$, and
$\varphi_{ij}$ pulls back $\xi_j$ to $\xi_i$; for the right: by
definition of $U_{ik}$). Moreover the cocycle condition
$\varphi_{jk}\circ\varphi_{ij}\circ\varphi_{ik}^{-1} =\mathrm{id}$ on $U_{ij}\cap U_{ik}$ holds trivially (both sides pull
$\xi_k$ back to $\xi_i$ there and the representing morphism is
unique). By the glueing lemma for schemes (Schemes, Lemma 26.14.2:
a scheme $X$ with an open covering $X=\bigcup_{i}U_i$ and isomorphisms
$\varphi_i:X_i\stackrel{\sim}{\to}U_i$ with the compatibility above
glues to a scheme; note the family is a set: the $X_i$ form a set) we
obtain a scheme $X$ over $S$ with open immersions
$X_i\hookrightarrow X$ whose intersections are the $U_{ij}$.

It remains to identify $X$ as a scheme representing $F$. The
elements $\xi_i\in F(X_i)=F(U_i)$ agree on the overlaps
($\varphi_{ij}^*\xi_j=\xi_i|_{U_{ij}}$), so by the Zariski sheaf
property (1) of $F$ there is a unique element
$\xi\in F(X)$ with $\xi|_{U_i}=\xi_i$; this gives a natural
transformation $h_X\to F$, $a^*\xi:=\xi\circ a$ for $a:T\to X$. It is
injective: if $a,b:T\to X$ with $a^*\xi=b^*\xi$, then the open
$T_i:=a^{-1}(U_i)$ is the largest open over which the pullback of
$\xi$ lies in $F_i$ (a property determined by
$a^*\xi=b^*\xi$), and over $T_i$ both $a$ and $b$ factor through
$X_i$, hence agree there because $X_i$ represents $F_i$ and
$\xi_i$ is universal: $a|_{T_i}=b|_{T_i}$; the Zariski sheaf property
of $h_X$ gives $a=b$. It is surjective: for $t\in F(T)$, the opens
$T_i:=t^{-1}(F_i)\subseteq T$ – the largest opens with
$t|_{T_i}\in F_i(T_i)$, well defined by (2)(b) – cover $T$ by
(2)(c); each $t|_{T_i}$ comes from a unique $a_i:T_i\to X_i$ (the
representability of $F_i$); on $T_i\cap T_j$ both $a_i$ and $a_j$
pull back the same element of $F$ (namely $t$), so by the
representability of $F_i$ (and by (2)(b)) they agree after the open
embeddings; the $a_i$'s glue to a unique $a:T\to X$ (the Zariski
sheaf property of $h_X$) and the construction gives
$a^*\xi=t$. Hence $h_X\cong F$ and $F$ is representable.
