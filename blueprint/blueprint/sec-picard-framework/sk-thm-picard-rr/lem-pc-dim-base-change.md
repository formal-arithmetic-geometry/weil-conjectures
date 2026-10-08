+++
id = "lem-pc-dim-base-change"
kind = "lemma"
title = "Dimension is unchanged under base change along field extensions"
order = 733
uses = ["def-pc-curve", "def-pc-dimension", "def-pc-field-tower", "def-pc-morphism-conventions"]
+++
Let $k$ be a field, $A$ a $k$-algebra of finite type and $K/k$ a field
extension. Then $\dim(A\otimes_kK)=\dim A$; hence for a
curve $X$ over $k$, the scheme
$X_K=X\times_{\operatorname{Spec} k}\operatorname{Spec} K$ has dimension $1$.

## Proof

Write $A=k[x_1,\dots,x_n]/I$, so $A\otimes_kK=K[x_1,\dots,x_n]/I\cdot K[x]$. For a Noetherian ring dimension formulas:
$\dim k[x]/I=n-\operatorname{ht}(I)$ (the classical formula for the
dimension of a quotient of a polynomial ring by the height of the
ideal), and the extension of an ideal under a faithfully flat ring map
preserves height: the map $k[x]\to K[x]$ is faithfully flat (base
change of the faithfully flat $k\to K$), and for flat ring maps
$\varphi:R\to R'$ and a prime $\mathfrak p\subset R$ one has
$\operatorname{ht}(\mathfrak pR')=\operatorname{ht}(\mathfrak p)$:
$\mathfrak pR'\cap R=\mathfrak p$ (faithful flatness: the tensor
$R/\mathfrak p\to R'/\mathfrak pR'$ is faithfully flat, hence
injective, so the preimage of $\mathfrak pR'$ is $\mathfrak p$), and
$\operatorname{ht}(\mathfrak pR')\ge\operatorname{ht}(\mathfrak p)$:
a chain $\mathfrak p_0\subsetneq\cdots\subsetneq\mathfrak p_r=\mathfrak p$
of primes of $R$ gives, by going-down for flat ring maps (Algebra,
Lemma 10.39.19, Tag [00HS](https://stacks.math.columbia.edu/tag/00HS)
(flatness implies going down for the map on spectra): the classical
statement, which says chains lift,
hence the height of the extended ideal is at least that of the source
ideal); and $\operatorname{ht}(\mathfrak pR')\le\operatorname{ht}(\mathfrak p)$:
a chain of primes in $R'$ above $\mathfrak pR'$ intersects $R$ in a
chain of primes all containing $\mathfrak p$ (again by
$\mathfrak q\cap R\supseteq\mathfrak p$ for $\mathfrak q\supseteq \mathfrak pR'$: flatness gives $\mathfrak q\cap R\supseteq\mathfrak p$
and the going-down property applied inside), i.e. a chain in $R$ from
$\mathfrak p$ down; so the two heights agree. Combining:
$\dim(A\otimes_kK)=n-\operatorname{ht}(I\cdot K[x]) =n-\operatorname{ht}(I)=\dim A$.
For the last assertion: $X$ is a curve, covered by affine opens
$\operatorname{Spec}(A_i)$ with $A_i$ finite type over $k$ and $\dim A_i\le1$ (and
$\dim X=\max_i\dim A_i=1$); the $X_K$ are covered by the
$\operatorname{Spec}(A_i\otimes_kK)$ of dimension $\dim A_i$, so $\dim X_K=1$.
