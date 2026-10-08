+++
id = "thm-trf-internal-hom-pullback"
kind = "theorem"
title = "Internal Hom versus pullback for a site-perfect first variable"
order = 2163
uses = ["def-trf-coefficient-conventions", "def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "def-weil-finite-tor-amplitude", "def-weil-scheme-morphism-properties", "def-weil-site-perfect-complex"]
+++
Use the finite coefficient ring
$A=A_{E,n}$. Let $g:Y'\to X$ be a
morphism of finite-type schemes,
let $M$ be a site-perfect complex
in $D(X,A)$, and let $N\in D^b_{ctf}(X,A)$ belong to the
finite-Tor constructible category.
The canonical comparison for
derived pullback and internal Hom
is an isomorphism

$$
Lg^*R\mathcal Hom_A(M,N)\xrightarrow{\sim}
R\mathcal Hom_A(Lg^*M,Lg^*N).
$$

It is natural in both variables and compatible with shifts and
distinguished triangles in $N$.

## Proof

By [def-weil-site-perfect-complex], locally on the site $M$ is
represented by a bounded complex $P$ of finite free $A$-modules.
Writing $M^\vee=R\mathcal Hom_A(M,A_X)$, the termwise finite-free
identity $\operatorname{Hom}_A(P^i,N^j)=(P^i)^\vee\otimes_A N^j$,
with the usual total-complex signs, gives

$$
M^\vee\otimes_A^L N\xrightarrow{\sim}R\mathcal Hom_A(M,N).
$$

There are finitely many summands in each total degree. Thus the same
identity computes the derived functors, and it is independent of the
chosen representative: the map is the adjoint of evaluation under the
tensor–Hom adjunction of [def-weil-derived-tensor]. These local
identifications therefore glue. The same argument identifies
$Lg^*M^\vee$ with $(Lg^*M)^\vee$: pull back the finite free complex
and its evaluation map. Monoidality of derived pullback, as in
[def-weil-derived-pullback-tensor-hom], now gives

$$
\begin{aligned}
Lg^*R\mathcal Hom_A(M,N)
&\cong Lg^*M^\vee\otimes_A^L Lg^*N\\
&\cong (Lg^*M)^\vee\otimes_A^L Lg^*N\\
&\cong R\mathcal Hom_A(Lg^*M,Lg^*N).
\end{aligned}
$$

The composite is the canonical comparison, since both have as adjoint
the pullback of evaluation. Evaluation is natural, and tensoring with
a fixed complex is exact; this proves the claimed compatibilities.
