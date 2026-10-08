+++
id = "prop-a1-curve-perverse-simples"
kind = "theorem"
tags = ["latex:proposition"]
title = "Simple perverse sheaves on a smooth curve"
order = 2748
uses = ["def-wf-middle-extension", "lem-weil-heart-short-exact-triangles", "lem-wf-dense-open-pi1-surjective", "thm-a1-curve-perverse-heart"]
+++
In the setting and with the conventions of [thm-a1-curve-perverse-heart],
the simple objects of the abelian category $\mathrm{Perv}(C)$ are the
following:

- the *punctual* objects $i_{x*}E$ (in degree $0$), where $x$ is a closed
  point of $C$ and $E$ is an irreducible sheaf on $x$, that is, an
  irreducible Weil module at $x$ in the Weil case;
- the *middle extensions* $(j_*\mathcal N)[1]$ of [def-wf-middle-extension],
  where $j:U\hookrightarrow C$ is a dense open immersion and $\mathcal N$
  is a nonzero irreducible lisse sheaf on $U$. Here irreducible means that
  $\mathcal N$ has no lisse subsheaf other than $0$ and $\mathcal N$.

Every object of either kind is simple, and every simple object is of one
of these kinds.

## Proof

We use the parts (1)–(5) of [thm-a1-curve-perverse-heart] freely.
"Punctual" and "no punctual subsheaf" are meant as there. We also use [lem-wf-dense-open-pi1-surjective] (SGA 1, Exposé V,
Proposition 8.2): for a dense open $k:U'\hookrightarrow U$ of a smooth
curve, the maps of fundamental groups and of Weil groups are surjective,
and consequently, for a lisse sheaf $\mathcal N$ on $U$, the unit
$\mathcal N\to k_*k^*\mathcal N$ is an isomorphism (part (3)) and, if
$\mathcal N$ is irreducible, so is $k^*\mathcal N$ (part (4)).

*Punctual objects are simple.* Let $E$ be irreducible, so $E\neq0$, and
let $0\to Q\to i_{x*}E\to R\to0$ be exact in $\mathrm{Perv}(C)$. Part (5)
gives $\mathcal H^{-1}Q=0$ and an exact sequence
$0\to\mathcal H^{-1}R\to\mathcal H^0Q\to i_{x*}E\to\mathcal H^0R\to0$.
Here $\mathcal H^{-1}R$ is a subsheaf of the punctual sheaf
$\mathcal H^0Q$, so it is punctual, and by (3) it is zero. So
$\mathcal H^0Q$ is a subsheaf of $i_{x*}E$. Subsheaves of $i_{x*}E$
correspond to submodules of $E$, since $i_{x*}$ is exact and fully
faithful with inverse $i_x^*$ on sheaves supported at $x$. Hence either
$\mathcal H^0Q=0$, and then $Q=0$, or $\mathcal H^0Q=i_{x*}E$, and then
$R=0$.

*Middle extensions are simple.* Let $P=(j_*\mathcal N)[1]$ with
$\mathcal N$ nonzero and irreducible, so $P\neq0$, and let
$0\to Q\to P\to R\to0$ be exact in $\mathrm{Perv}(C)$. Part (5) gives
$\mathcal H^0R=0$ and an exact sequence
$$
0\to\mathcal H^{-1}Q\to j_*\mathcal N\to\mathcal H^{-1}R\to
\mathcal H^0Q\to0 .
$$
Choose a dense open $k:U'\hookrightarrow U$ on which $\mathcal H^{-1}Q$
and $\mathcal H^{-1}R$ are lisse and the punctual sheaf $\mathcal H^0Q$
vanishes, and write $j'=j\circ k$. On $U'$ we get an exact sequence of
lisse sheaves $0\to\mathcal H^{-1}Q|_{U'}\to\mathcal N|_{U'}\to
\mathcal H^{-1}R|_{U'}\to0$. Since $\mathcal N|_{U'}$ is irreducible,
there are two cases.

(a) Suppose $\mathcal H^{-1}Q|_{U'}=0$. Then $\mathcal H^{-1}Q$ is a
punctual subsheaf of $j_*\mathcal N$, so it is zero by (3) and (4), and
$\mathcal N|_{U'}\cong\mathcal H^{-1}R|_{U'}$. Put
$\mathcal H:=\mathcal H^{-1}R$. By (3) it has no punctual subsheaf, so
the unit $\mathcal H\to j'_*j'^*\mathcal H$ is injective, because its
kernel is punctual. The composite
$$
j_*\mathcal N\to\mathcal H\to j'_*j'^*\mathcal H
\cong j'_*(\mathcal N|_{U'})=j_*k_*k^*\mathcal N
$$
is $j_*$ of the unit $\mathcal N\to k_*k^*\mathcal N$, which is an
isomorphism. Hence the injective second map is also surjective, and so
$j_*\mathcal N\to\mathcal H$ is an isomorphism. Its cokernel
$\mathcal H^0Q$ therefore vanishes, and $Q=0$. This is the step that
excludes a punctual subobject of the middle extension.

(b) Suppose $\mathcal H^{-1}Q|_{U'}=\mathcal N|_{U'}$. Then
$\mathcal H^{-1}R$ vanishes on $U'$, so it is punctual, hence zero by
(3). Then $R=0$, and $Q\to P$ is an isomorphism.

*Every simple object is of one of the two kinds.* Let $P$ be simple. The
exact sequence $0\to(\mathcal H^{-1}P)[1]\to P\to(\mathcal H^0P)[0]\to0$
of (5) forces either $\mathcal H^{-1}P=0$ or $\mathcal H^0P=0$.

If $\mathcal H^{-1}P=0$, then $P=\mathcal G[0]$ with $\mathcal G$
punctual, supported on a finite set of closed points, so
$\mathcal G\cong\bigoplus_xi_{x*}\mathcal G_x$. Every subsheaf
$\mathcal G'\subset\mathcal G$ gives a short exact sequence
$0\to\mathcal G'[0]\to\mathcal G[0]\to(\mathcal G/\mathcal G')[0]\to0$ in
the heart. This holds because the three terms are punctual, hence in the
heart by (3), and they form a distinguished triangle, so part (4)
of [lem-weil-heart-short-exact-triangles] applies. By simplicity
$\mathcal G$ has no subsheaves other than $0$ and $\mathcal G$. So
$\mathcal G=i_{x*}E$ for a single closed point $x$ and an irreducible $E$.

If $\mathcal H^0P=0$, then $P=\mathcal F[1]$ with $\mathcal F\neq0$
having no punctual subsheaf. Choose a dense open $j:U\hookrightarrow C$
on which $\mathcal F$ is lisse, and put $\mathcal N:=j^*\mathcal F$. The
unit $\mathcal F\to j_*\mathcal N$ is injective, because its kernel is
punctual. In particular $\mathcal N\neq0$. Let $\mathcal Q$ be its
cokernel. It vanishes on $U$, so it is punctual. The sheaf sequence
$0\to\mathcal F\to j_*\mathcal N\to\mathcal Q\to0$ gives a distinguished
triangle $\mathcal Q[0]\to\mathcal F[1]\to(j_*\mathcal N)[1]\to$ whose
three terms lie in the heart by (3) and (4). So it is a short exact
sequence in $\mathrm{Perv}(C)$ by part (4) of
[lem-weil-heart-short-exact-triangles]. Its quotient $(j_*\mathcal N)[1]$ is
nonzero, so simplicity forces $\mathcal Q=0$, and hence
$P\cong(j_*\mathcal N)[1]$.

It remains to show that $\mathcal N$ is irreducible. Let
$0\neq\mathcal N'\subsetneq\mathcal N$ be a lisse subsheaf, and let
$\mathcal C$ be the cokernel of $j_*\mathcal N'\to j_*\mathcal N$. Let
$\mathcal C'' := \mathcal C/\mathcal C_{\mathrm p}$ be its quotient by
its largest punctual subsheaf, and let
$\mathcal F':=\ker(j_*\mathcal N\to\mathcal C'')$. The sequence
$0\to\mathcal F'\to j_*\mathcal N\to\mathcal C''\to0$ has no punctual
subsheaf in any of its terms: $\mathcal F'$ is a subsheaf of
$j_*\mathcal N$, and $\mathcal C''$ has none by construction. So, as
above, it gives a short exact sequence
$0\to\mathcal F'[1]\to P\to\mathcal C''[1]\to0$ in $\mathrm{Perv}(C)$.
On $U$ the sheaf $\mathcal C|_U=\mathcal N/\mathcal N'$ is lisse, so
$\mathcal C_{\mathrm p}|_U=0$ and $\mathcal F'|_U=\mathcal N'$. Both
$\mathcal F'$ and $\mathcal C''$ are therefore nonzero, and this
contradicts the simplicity of $P$. Hence $\mathcal N$ is irreducible, and
$P$ is a middle extension of the second kind.
