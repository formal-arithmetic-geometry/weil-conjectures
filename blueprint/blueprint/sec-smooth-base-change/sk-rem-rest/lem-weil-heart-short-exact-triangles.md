+++
id = "lem-weil-heart-short-exact-triangles"
kind = "lemma"
title = "Short exact sequences in the heart are triangles"
order = 1447
uses = ["def-weil-t-structure", "prop-weil-heart-abelian"]
+++
Let $(\mathcal T^{\le0},\mathcal T^{\ge0})$ be a t-structure on a
triangulated category $\mathcal T$ in the sense of [def-weil-t-structure]
(not necessarily bounded), and let $\mathcal A=\mathcal
T^{\le0}\cap\mathcal T^{\ge0}$ be its heart, which is abelian by
[prop-weil-heart-abelian].

1. (*Truncations.*) For every $K\in\mathcal T$ and $n\in\mathbf Z$ the
   triangle $\tau^{\le n}K\to K\to\tau^{\ge n+1}K\to\tau^{\le n}K[1]$ with
   $\tau^{\le n}K\in\mathcal T^{\le n}$ and $\tau^{\ge n+1}K\in\mathcal
   T^{\ge n+1}$ is unique up to unique isomorphism, and $\tau^{\le n}$,
   $\tau^{\ge n+1}$ are functors, right, respectively left, adjoint to the
   inclusions of $\mathcal T^{\le n}$ and $\mathcal T^{\ge n+1}$. There is
   a canonical isomorphism $\tau^{\ge0}\tau^{\le0}\cong\tau^{\le0}\tau^{\ge0}$,
   and $H^0:=\tau^{\ge0}\tau^{\le0}:\mathcal T\to\mathcal A$; put
   $H^i(K):=H^0(K[i])$.
2. (*Extensions.*) $\mathcal T^{\le n}$, $\mathcal T^{\ge n}$ and
   $\mathcal A$ are closed under extensions: if $X\to Y\to Z\to X[1]$ is
   distinguished and $X,Z$ lie in one of them, so does $Y$.
3. (*Kernels and cokernels.*) Let $f:X\to Y$ be a morphism of $\mathcal A$
   and complete it to a distinguished triangle $X\xrightarrow fY\to S\to
   X[1]$. Then $S\in\mathcal T^{\le0}\cap\mathcal T^{\ge-1}$,
   $$
   \ker f\cong H^{-1}(S)=(\tau^{\le-1}S)[-1],\qquad
   \operatorname{coker}f\cong H^0(S)=\tau^{\ge0}S,
   $$
   with the kernel map $(\tau^{\le-1}S)[-1]\to S[-1]\to X$ and the
   cokernel map $Y\to S\to\tau^{\ge0}S$.
4. (*Short exact sequences.*) A sequence $0\to X\xrightarrow fY
   \xrightarrow gZ\to0$ of $\mathcal A$ is short exact if and only if
   there is a morphism $\delta:Z\to X[1]$ such that $X\xrightarrow fY
   \xrightarrow gZ\xrightarrow\delta X[1]$ is distinguished, and then
   $\delta$ is unique. In particular a distinguished triangle whose three
   terms lie in $\mathcal A$ is a short exact sequence of $\mathcal A$.
5. (*Cohomological functor.*) $H^0$ is cohomological: a distinguished
   triangle $X\to Y\to Z\to X[1]$ gives a long exact sequence in
   $\mathcal A$
   $$
   \cdots\to H^{i}(X)\to H^{i}(Y)\to H^{i}(Z)\to H^{i+1}(X)\to\cdots .
   $$

(*Source: Beilinson--Bernstein--Deligne, Faisceaux pervers, 1.3.3--1.3.6
and 1.1.9--1.1.10; no Stacks Project entry states this form, for the
reasons recorded at [def-weil-t-structure].*)

## Proof

Throughout, axiom 1 of [def-weil-t-structure] gives $\mathcal T^{\le
n-1}\subseteq\mathcal T^{\le n}$ and $\mathcal T^{\ge n+1}\subseteq
\mathcal T^{\ge n}$, and axiom 2, shifted, gives $\Hom(A,B)=0$ for
$A\in\mathcal T^{\le n}$, $B\in\mathcal T^{\ge n+1}$. We use the long exact
$\Hom$ sequences of distinguished triangles freely.

*(1).* Let $A\to K\to B\to A[1]$ be a triangle as in axiom 3 (shifted to
level $n$). For $A'\in\mathcal T^{\le n}$ the sequence
$\Hom(A',B[-1])\to\Hom(A',A)\to\Hom(A',K)\to\Hom(A',B)$ has both outer
terms zero ($B[-1],B\in\mathcal T^{\ge n+1}$), so $A$ represents
$\Hom(-,K)$ on $\mathcal T^{\le n}$. Hence $A=:\tau^{\le n}K$ is unique up
to unique isomorphism and functorial in $K$, right adjoint to the
inclusion; dually $B=:\tau^{\ge n+1}K$ represents $\Hom(K,-)$ on $\mathcal
T^{\ge n+1}$. The third morphism is unique because $\Hom(A[1],B)=0$ (the
argument of (4) below). Two consequences: $K\in\mathcal T^{\le n}$ iff
$\tau^{\ge n+1}K=0$, and $K\in\mathcal T^{\ge n+1}$ iff $\Hom(A',K)=0$ for
all $A'\in\mathcal T^{\le n}$ (then $\tau^{\le n}K\to K$ is zero, so
$\tau^{\le n}K=0$); dually $\mathcal T^{\le n}$ is the left orthogonal of
$\mathcal T^{\ge n+1}$. For $K\in\mathcal T^{\le0}$ the object
$\tau^{\ge0}K$ is an extension of $K$ and $(\tau^{\le-1}K)[1]$, so it lies
in $\mathcal T^{\le0}$ by (2) (whose proof uses only the orthogonality just
shown); dually $\tau^{\le0}$ preserves $\mathcal T^{\ge0}$. So $H^0$ takes
values in $\mathcal A$. For the commutation, the octahedral axiom applied
to $\tau^{\le-1}K\to\tau^{\le0}K\to K$ (the first map is the truncation of
$\tau^{\le0}K$, since both represent $\Hom(-,K)$ on $\mathcal T^{\le-1}$)
gives a distinguished triangle
$\tau^{\ge0}\tau^{\le0}K\to\tau^{\ge0}K\to\tau^{\ge1}K\to$, whose first
term lies in $\mathcal T^{\le0}$ and whose third lies in $\mathcal
T^{\ge1}$. By uniqueness it is the truncation triangle of $\tau^{\ge0}K$,
so $\tau^{\ge0}\tau^{\le0}K\cong\tau^{\le0}\tau^{\ge0}K$.

*(2).* By (1), $\mathcal T^{\ge n+1}$ is the right orthogonal of $\mathcal
T^{\le n}$, and a right orthogonal is closed under extensions: for
$A'\in\mathcal T^{\le n}$ the sequence
$\Hom(A',X)\to\Hom(A',Y)\to\Hom(A',Z)$ is exact with zero outer terms.
Dually for $\mathcal T^{\le n}$, and $\mathcal A$ is the intersection.

*(3).* The object $S$ is an extension of $Y$ and $X[1]$, both in
$\mathcal T^{\le0}\cap\mathcal T^{\ge-1}$, so $S$ lies there by (2);
consequently $\tau^{\le-1}S\in\mathcal T^{\le-1}\cap\mathcal T^{\ge-1}$
and $\tau^{\ge0}S\in\mathcal A$ by (1), and these are $H^{-1}(S)[1]$ and
$H^0(S)$. Let $T\in\mathcal A$. The sequence
$\Hom(X[1],T)\to\Hom(S,T)\to\Hom(Y,T)\to\Hom(X,T)$ is exact with
$\Hom(X[1],T)=0$, and $\Hom(\tau^{\ge0}S,T)=\Hom(S,T)$ by adjunction. So
$\Hom(\tau^{\ge0}S,T)$ is the set of $h:Y\to T$ with $hf=0$, that is,
$Y\to\tau^{\ge0}S$ is a cokernel of $f$. Dually, $\Hom(T,Y[-1])=0$ and
$\Hom(T,(\tau^{\le-1}S)[-1])=\Hom(T,\tau^{\le0}(S[-1]))=\Hom(T,S[-1])$, so
$\Hom(T,(\tau^{\le-1}S)[-1])$ is the set of $h:T\to X$ with $fh=0$, and
$(\tau^{\le-1}S)[-1]\to X$ is a kernel of $f$.

*(4).* Keep the triangle of (3). If $X\xrightarrow fY\xrightarrow gZ
\xrightarrow\delta X[1]$ is distinguished with $Z\in\mathcal A$, then
$S\cong Z\in\mathcal T^{\ge0}$, so $\tau^{\le-1}S=0$ and $\ker f=0$, while
$\tau^{\ge0}S=S$, so $g$ is a cokernel of $f$ by (3); the sequence is short
exact. Conversely, let $0\to X\to Y\to Z\to0$ be short exact. Then $\ker
f=0$ gives $\tau^{\le-1}S=0$ by (3), so $S\in\mathcal A$ and $Y\to S$ is a
cokernel of $f$. The unique isomorphism $S\cong Z$ under $Y$ carries the
triangle of (3) to a distinguished triangle $X\to Y\to Z\to X[1]$. If
$\delta,\delta'$ both complete $(f,g)$, the morphism axiom gives
$h:Z\to Z$ with $hg=g$ and $\delta'h=\delta$. Then $(h-1)g=0$, so
$h-1$ factors through $\delta$ via some $X[1]\to Z$; but
$\Hom(X[1],Z)=0$ because $X[1]\in\mathcal T^{\le-1}$ and $Z\in\mathcal
T^{\ge0}$. So $h=1$ and $\delta'=\delta$.

*(5).* Rotating triangles, it suffices to show that $H^0X\to H^0Y\to H^0Z$
is exact at $H^0Y$ for every distinguished $X\to Y\to Z\to X[1]$.

(a) If $X,Y,Z\in\mathcal T^{\ge0}$, then $0\to H^0X\to H^0Y\to H^0Z$ is
exact: for $K\in\mathcal T^{\ge0}$ and $T\in\mathcal A$, (1) gives
$H^0K=\tau^{\le0}K$ and $\Hom(T,H^0K)=\Hom(T,K)$, and
$0=\Hom(T,Z[-1])\to\Hom(T,X)\to\Hom(T,Y)\to\Hom(T,Z)$ is exact; conclude by
Yoneda in the abelian category $\mathcal A$. Dually, if $X,Y,Z\in\mathcal
T^{\le0}$, then $H^0X\to H^0Y\to H^0Z\to0$ is exact, using
$\Hom(H^0K,T)=\Hom(K,T)$ for $K\in\mathcal T^{\le0}$.

(b) If $Z\in\mathcal T^{\ge0}$, the octahedral axiom applied to
$\tau^{\le-1}X\to X\to Y$ gives distinguished triangles
$\tau^{\le-1}X\to Y\to Y''\to$ and $\tau^{\ge0}X\to Y''\to Z\to$. By (2)
$Y''\in\mathcal T^{\ge0}$, so the first is the truncation triangle and
$Y''\cong\tau^{\ge0}Y$. Since $H^0\tau^{\ge0}=H^0$ by the commutation in
(1), (a) applied to $\tau^{\ge0}X\to\tau^{\ge0}Y\to Z$ gives the exact
sequence $0\to H^0X\to H^0Y\to H^0Z$. Dually, if $X\in\mathcal T^{\le0}$,
applying the octahedral axiom to $Y\to Z\to\tau^{\ge1}Z$ gives a
triangle $X\to\tau^{\le0}Y\to\tau^{\le0}Z\to$ and an exact sequence
$H^0X\to H^0Y\to H^0Z\to0$.

(c) In general, apply the octahedral axiom to $\tau^{\le0}X\to X\to Y$.
It gives distinguished triangles $\tau^{\le0}X\to Y\to W\to$ and
$\tau^{\ge1}X\to W\to Z\to$, with $Y\to W\to Z$ equal to the given map
$Y\to Z$. By the second half of (b), $H^0X=H^0\tau^{\le0}X\to H^0Y\to
H^0W\to0$ is exact. Rotating the second triangle to $W\to Z\to
(\tau^{\ge1}X)[1]\to W[1]$, whose third term lies in $\mathcal T^{\ge0}$,
the first half of (b) shows that $H^0W\to H^0Z$ is a monomorphism. Hence
$\ker(H^0Y\to H^0Z)=\ker(H^0Y\to H^0W)=\operatorname{im}(H^0X\to H^0Y)$.
