+++
id = "lem-trf-local-term-locality"
kind = "lemma"
title = "Locality and zero-stalk vanishing of the local term"
order = 2342
uses = ["d-curve-pieces", "def-trf-correspondence", "def-trf-frobenius-coefficient-morphism", "def-trf-graph-correspondence", "def-trf-iterated-weil-map", "def-trf-local-term", "def-trf-trace-class-source", "lem-trf-local-term-point", "lem-trf-trace-map-from-external-duality", "thm-trf-frobenius-fixed-points"]
+++
Let $c=(c_1,c_2):C\to X\times X$ be an admissible correspondence with
$\operatorname{Fix}(c)=F$, coefficient $K\in D^b_{ctf}(X,A)$ and
$u:c_2^*K\to c_1^!K$ ([def-trf-correspondence]), and let $y\in F(k)$ be a
geometric fixed point which is an open-and-closed component of $F$. Say
that $c$ is *contracting at $y$* if $c_1^{-1}(y)$ is the reduced point $y$,
$c_2(y)=y$, and the ideal sheaves on $C$ satisfy

$$
c_2^{\cdot}(\mathcal I_y)^n\subset\mathcal I_{y,C}^{\,n+1}\qquad\text{for some }n\geq1,
$$

where $\mathcal I_{y,C}=c_1^{\cdot}(\mathcal I_y)\mathcal O_C$ is the ideal of
the reduced point $y\subset C$. This is Varshavsky's "$c$ stabilizes
$Z=\{y\}$ and is contracting near $Z$"
([Def. 2.1.1](https://arxiv.org/abs/math/0505564)), with the two legs
interchanged to match the convention $u:c_2^*K\to c_1^!K$; the stabilizing
inclusion $c_2^{\cdot}(\mathcal I_y)\subset\mathcal I_{y,C}$ follows from
$c_2(y)=y$, and the condition holds with $n=1$ whenever the map induced by
$c_2$ on the cotangent space at $y$ is zero.

1. (Contracting local terms.) If $c$ is contracting at $y$, then the
restriction $\operatorname{Tr}_c(u)|_y$, and hence the local term
$\operatorname{LT}_y(u)$ of [def-trf-local-term], depend only on the stalk
$K_{\bar y}$ and on the stalk map $u_{\bar y}:K_{\bar y}\to K_{\bar y}$
induced by $u$ (via $c_2(y)=y=c_1(y)$):
$\operatorname{LT}_y(u)=\operatorname{tr}_A(u_{\bar y}\mid K_{\bar y})$.
No invertibility of $u$ is required.
1. (Zero-stalk vanishing.) If $c$ is contracting at $y$ and $K_{\bar y}=0$,
then $\operatorname{Tr}_c(u)|_y=0$ and $\operatorname{LT}_y(u)=0$, for
every coefficient morphism $u$.
1. (Smooth-curve form.) In the smooth-curve setting of
[d-curve-pieces] — $X_0$ smooth of pure dimension one, $m\ge1$,
$x\in X_0(\mathbf F_{q^m})$ with geometric point $\bar x$ — let
$v:L\Phi^{m*}K\to K$ be either the scheme-Frobenius map
$u_m=\varphi^{[m]}\circ\kappa^{(m)}_K$ of [def-trf-iterated-weil-map]
(the map written $\varphi_m$ in [d-curve-pieces]) or an arbitrary,
not necessarily invertible, Frobenius coefficient morphism
$L\Phi^{m*}K\to K$ (in the sense of
[def-trf-frobenius-coefficient-morphism] for $\Phi^m$, the
$q^m$-power Frobenius of $X_0\times_{k_0}\mathbf F_{q^m}$; for
instance the iterate $\psi_m$ of a Frobenius coefficient morphism
$\psi$), and consider the graph correspondence of
$(\Phi^m,v)$ of [def-trf-graph-correspondence], assumed admissible
as throughout so that its trace class is defined. If $K_{\bar x}=0$,
then the local term $\operatorname{LT}_{\bar x}(v)$ at the fixed
point $\bar x$ is zero.

## Proof

*The stalk of the trace-class source.* By [def-trf-trace-class-source]
the source is $\mathcal H_c(K)=R\mathcal Hom_A(c_2^*K,c_1^!K)$. Its stalk
at $y$ is **not** $R\mathcal Hom_A(K_{\bar y},K_{\bar y})$: restriction to
a point commutes with $i^!$ on internal Hom, but not with $i^*$. For
$X=\mathbf A^1$, $j:\mathbf G_m\hookrightarrow X$, $K=j_!A$ and the graph
of a Frobenius (so that $c_2^*K\simeq K$ and $c_1^!K=K$), internal-Hom
adjunction gives $R\mathcal Hom_A(j_!A,j_!A)\simeq Rj_*A$, whose
degree-zero stalk at $0$ is $A$ (the punctured strictly henselian curve is
connected), although $K_0=0$. Hence (1) and (2) cannot be read off from
the stalk: the trace map of [lem-trf-trace-map-from-external-duality] is
local on $F$, but its source at $y$ sees more than $(K_{\bar y},u_{\bar y})$.
A nonzero source can still map to zero, and for contracting correspondences
it does; this is the content of (1) and (2).

*(1) and (2).* These are the contracting-correspondence theorem of
Varshavsky, [Thm. 2.1.3](https://arxiv.org/abs/math/0505564), translated
into the present conventions. In Varshavsky's convention a $c$-morphism is
$c_1^*\mathcal F\to c_2^!\mathcal F$; interchanging the legs, his
hypothesis "$c$ stabilizes $Z$ and is contracting near $Z$" for
$Z=\{y\}$ reads
$c_2^{\cdot}(\mathcal I_y)\subset c_1^{\cdot}(\mathcal I_y)\mathcal O_C$ and
$c_2^{\cdot}(\mathcal I_y)^n\subset(c_1^{\cdot}(\mathcal I_y)\mathcal O_C)^{n+1}$,
which is the hypothesis above. His conclusion, for the open-and-closed
component $\beta=\{y\}$ of $F$, which meets $Z$, is
$\operatorname{Tr}_c(u)|_y=\operatorname{Tr}_{c|_Z}(u|_Z)|_y$ and
$\operatorname{LT}_y(u)=\operatorname{LT}_y(u|_Z)$, where
$c|_Z:c_1^{-1}(Z)_{\mathrm{red}}\to Z\times Z$ is the correspondence
induced on $Z$ and $u|_Z$ the restricted coefficient morphism (his 1.5.6).
Since $c_1^{-1}(y)=y$ is reduced, $c|_Z$ is the identity correspondence of
the point $y\cong\Spec k$, with coefficient $K_{\bar y}$ and morphism the
stalk map $u_{\bar y}$; its local term is
$\operatorname{tr}_A(u_{\bar y}\mid K_{\bar y})$ by
[lem-trf-local-term-point]. This proves (1), and (2) is the case
$K_{\bar y}=0$, where $\operatorname{tr}_A(0\mid0)=0$. Varshavsky's theorem
is proved by specialization to the normal cone of $Z$ (his §§1.3–1.4 and
2.1); it holds for every $c$-morphism and for the finite coefficient rings
$A=A_{E,n}$ (his §1.1), and nothing is inverted. Its proof reduces, via
the additivity of trace classes along the open–closed decomposition
$X=Z\sqcup U$ and proper pushforward from $Z$, precisely to the vanishing
(2) for $j_!j^*K$, which is then shown by the normal-cone argument; the
blueprint quotes this argument and does not reprove it.

*(3).* The graph correspondence of $(\Phi^m,v)$ has
$C=X$, $c_1=\operatorname{id}_X$, $c_2=\Phi^m$ and fixed scheme
$\operatorname{Fix}(\Phi^m)$ by [def-trf-graph-correspondence]. By
[thm-trf-frobenius-fixed-points] this fixed scheme is the disjoint
union of copies of $\Spec k$, one for each point of
$X_0(\mathbf F_{q^m})$; in particular it is finite over $k$, hence
proper with finitely many open-and-closed components, so the local
terms of [def-trf-local-term] are defined, and the geometric point
$\bar x$ over $x$ is one of these components, an isolated reduced fixed
point. The graph is contracting at $\bar x$: $c_1^{-1}(\bar x)=\bar x$,
$\Phi^m(\bar x)=\bar x$, and if $t_i$ are affine coordinates with
$a_i=t_i(x)\in\mathbf F_{q^m}$, then
$\Phi^{m\cdot}(t_i-a_i)=t_i^{q^m}-a_i=(t_i-a_i)^{q^m}$, so
$\Phi^{m\cdot}(\mathcal I_{\bar x})\mathcal O_X\subset\mathcal I_{\bar x}^{\,q^m}\subset\mathcal I_{\bar x}^{\,2}$
as $q^m\geq2$; this holds for every separated finite-type $X_0$, not only
for curves. Its stalk map is
$v_{\bar x}:K_{\bar x}=(L\Phi^{m*}K)_{\bar x}\to K_{\bar x}$, using
$\Phi^m(\bar x)=\bar x$. Applying (2) with $y=\bar x$ and $u=v$ gives
$\operatorname{LT}_{\bar x}(v)=0$ when $K_{\bar x}=0$; since (1) and
(2) use no invertibility of $u$, this holds both for the
scheme-Frobenius map $u_m$ and for an arbitrary Frobenius coefficient
morphism.
